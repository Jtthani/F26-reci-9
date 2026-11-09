import { describe, expect, it } from 'vitest';
import fc from 'fast-check';
import { mergeIntervals, type Interval } from '../src/intervals';

// Read the spec in src/intervals/mergeIntervals.ts, then check your progress
// with `npm run mutants:intervals`.
//
// Label every property with its pattern, on the line above its `it(`:
//   // Pattern: invariant. The output is sorted.
// (invariant, algebraic, metamorphic, differential, or conditional)

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

// The first draft used fc.tuple(fc.integer(), fc.integer()), which produced
// intervals like [0, -1] that break the precondition start <= end, so the
// correct implementation (rightly) threw. Instead of filtering those out, we
// construct valid intervals: pick a start and a non-negative length, and set
// end = start + length.
//
// Coordinates are kept small on purpose. That makes overlaps, intervals that
// share an endpoint exactly ([1, 3] and [3, 5]), gaps of exactly one
// ([1, 2] and [3, 4]), duplicates, and zero-length intervals ([3, 3]) common,
// which is where merging bugs hide. Negative values and mixed digit counts
// (-15, -3, 7, 12) are included, so the order of starts matters.
const coord = fc.integer({ min: -20, max: 20 });
const interval: fc.Arbitrary<Interval> = fc
  .tuple(coord, fc.nat(8))
  .map(([start, length]): Interval => [start, start + length]);
const intervalList = fc.array(interval);

// The same list together with a shuffled copy of it.
const listAndShuffle = intervalList.chain(xs =>
  fc.tuple(fc.constant(xs), fc.shuffledSubarray(xs, { minLength: xs.length, maxLength: xs.length })),
);

// Targeted generator for already-disjoint input. Walk from left to right:
// each interval starts at least 1 past the previous interval's end, so no two
// intervals overlap or touch. A gap of exactly 1 is the most common case
// (fast-check favours the bounds), which is the "[1, 2] and [3, 4] stay
// separate" case from the spec. The result is in sorted order.
const disjointSorted: fc.Arbitrary<Interval[]> = fc
  .tuple(coord, fc.array(fc.tuple(fc.integer({ min: 1, max: 4 }), fc.nat(5))))
  .map(([first, steps]) => {
    const out: Interval[] = [];
    let start = first;
    for (const [gap, length] of steps) {
      out.push([start, start + length]);
      start += length + gap;
    }
    return out;
  });
// ...and the same intervals in a random order (the input may be in any order).
const disjointAndShuffled = disjointSorted.chain(sorted =>
  fc.tuple(
    fc.constant(sorted),
    fc.shuffledSubarray(sorted, { minLength: sorted.length, maxLength: sorted.length }),
  ),
);

// Targeted generator for intervals that all contain a common point p:
// [p - left, p + right]. A left or right of 0 gives intervals that only
// touch at p, such as [p - 2, p] and [p, p + 3].
const sharingAPoint: fc.Arbitrary<Interval[]> = fc
  .tuple(coord, fc.array(fc.tuple(fc.nat(8), fc.nat(8)), { minLength: 1 }))
  .map(([p, arms]) => arms.map(([left, right]): Interval => [p - left, p + right]));

// Intervals that break the precondition, constructed one kind at a time so
// each part of the check (start <= end, integer start, integer end) is tested
// on its own.
const fraction = fc.integer({ min: 1, max: 99 }).map(n => n / 100);
const badInterval: fc.Arbitrary<Interval> = fc.oneof(
  // start > end
  fc.tuple(coord, fc.integer({ min: 1, max: 10 })).map(([end, d]): Interval => [end + d, end]),
  // start is not an integer (start <= end still holds)
  fc.tuple(coord, fraction, fc.nat(8)).map(([n, f, length]): Interval => [n - f, n + length]),
  // end is not an integer (start <= end still holds)
  fc.tuple(coord, fraction, fc.nat(8)).map(([n, f, length]): Interval => [n, n + length + f]),
  // NaN and the infinities are not integers either
  fc.constantFrom<Interval>([-Infinity, 0], [0, Infinity], [-Infinity, Infinity], [NaN, 0], [0, NaN]),
);
// A valid list with one bad interval inserted at a random position.
const listWithBadInterval: fc.Arbitrary<Interval[]> = fc
  .tuple(intervalList, badInterval)
  .chain(([xs, bad]) =>
    fc.nat(xs.length).map(i => [...xs.slice(0, i), bad, ...xs.slice(i)]),
  );

// ---------------------------------------------------------------------------
// Small helpers (oracles, not a re-implementation)
// ---------------------------------------------------------------------------

/** Is point p inside some interval of the list? */
const covers = (list: readonly Interval[], p: number): boolean =>
  list.some(([s, e]) => s <= p && p <= e);

/**
 * Points worth probing. Coverage can only change at an endpoint, so it is
 * enough to probe every endpoint, one point strictly between each pair of
 * neighbouring endpoints (that is where non-integer gaps such as 2 < x < 3
 * live), and one point beyond each end.
 */
function probePoints(...lists: (readonly Interval[])[]): number[] {
  const ends = [...new Set(lists.flatMap(list => list.flat()))].sort((a, b) => a - b);
  if (ends.length === 0) return [0];
  const between = ends.slice(1).map((e, i) => (ends[i] + e) / 2);
  return [ends[0] - 1, ...ends, ...between, ends[ends.length - 1] + 1];
}

const copy = (xs: readonly Interval[]): Interval[] => xs.map(([s, e]): Interval => [s, e]);
const shift = (xs: readonly Interval[], k: number): Interval[] =>
  xs.map(([s, e]): Interval => [s + k, e + k]);

// ---------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------

describe('mergeIntervals', () => {
  // Pattern: invariant. Every input interval lies inside some output interval.
  it('every input interval lies inside some output interval', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        const uncovered = xs.filter(([s, e]) => !out.some(([a, b]) => a <= s && e <= b));
        expect(uncovered).toEqual([]);
      }),
    );
  });

  // Pattern: invariant. Every output interval has integer endpoints with start <= end, the output is sorted by start, and consecutive intervals neither overlap nor touch (result[i][1] < result[i + 1][0]).
  it('returns well-formed, sorted intervals that neither overlap nor touch', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        const malformed = out.filter(([s, e]) => !(Number.isInteger(s) && Number.isInteger(e) && s <= e));
        expect(malformed).toEqual([]);
        const badNeighbours = out.slice(1).filter((next, i) => !(out[i][1] < next[0]));
        expect(badNeighbours).toEqual([]);
      }),
    );
  });

  // Pattern: invariant. The input array and the intervals in it are not modified.
  it('does not modify the input array or its intervals', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const before = copy(xs);
        const sameObjects = [...xs];
        mergeIntervals(xs);
        expect(xs).toEqual(before);
        expect(xs.every((iv, i) => iv === sameObjects[i])).toBe(true);
      }),
    );
  });

  // Pattern: differential. For every real point p, p is covered by the output exactly when it is covered by the input.
  it('covers exactly the same points (including non-integers) as the input', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        const mismatches = probePoints(xs, out).filter(p => covers(xs, p) !== covers(out, p));
        expect(mismatches).toEqual([]);
      }),
    );
  });

  // Pattern: metamorphic. Shuffling the input does not change the output.
  it('gives the same result for any order of the input', () => {
    fc.assert(
      fc.property(listAndShuffle, ([xs, shuffled]) => {
        expect(mergeIntervals(shuffled)).toEqual(mergeIntervals(xs));
      }),
    );
  });

  // Pattern: metamorphic. Repeating every interval (adding duplicates) does not change the output.
  it('ignores duplicate intervals', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        expect(mergeIntervals([...xs, ...copy(xs)])).toEqual(mergeIntervals(xs));
      }),
    );
  });

  // Pattern: metamorphic. Shifting every input interval by k shifts every output interval by k.
  it('commutes with shifting every interval by the same amount', () => {
    fc.assert(
      fc.property(intervalList, fc.integer({ min: -50, max: 50 }), (xs, k) => {
        expect(mergeIntervals(shift(xs, k))).toEqual(shift(mergeIntervals(xs), k));
      }),
    );
  });

  // Pattern: algebraic. Merging is idempotent: merging an already-merged list gives the same list back.
  it('is idempotent', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const once = mergeIntervals(xs);
        expect(mergeIntervals(once)).toEqual(once);
      }),
    );
  });

  // Pattern: algebraic. Merging two lists together equals merging each list first and then merging the two results.
  it('merge(xs ++ ys) equals merge(merge(xs) ++ merge(ys))', () => {
    fc.assert(
      fc.property(intervalList, intervalList, (xs, ys) => {
        expect(mergeIntervals([...xs, ...ys])).toEqual(
          mergeIntervals([...mergeIntervals(xs), ...mergeIntervals(ys)]),
        );
      }),
    );
  });

  // Pattern: conditional. If no two input intervals overlap or touch, the output is exactly the input intervals sorted by start.
  it('returns already-disjoint input sorted and otherwise unchanged', () => {
    fc.assert(
      fc.property(disjointAndShuffled, ([sorted, shuffled]) => {
        expect(mergeIntervals(shuffled)).toEqual(sorted);
      }),
    );
  });

  // Pattern: conditional. If every input interval contains a common point, the output is the single interval [smallest start, largest end].
  it('merges intervals that share a point into one interval', () => {
    fc.assert(
      fc.property(sharingAPoint, xs => {
        const lo = Math.min(...xs.map(([s]) => s));
        const hi = Math.max(...xs.map(([, e]) => e));
        expect(mergeIntervals(xs)).toEqual([[lo, hi]]);
      }),
    );
  });

  // Pattern: conditional. If any interval has a non-integer endpoint or start > end, mergeIntervals throws a RangeError.
  it('throws a RangeError when any interval breaks the preconditions', () => {
    fc.assert(
      fc.property(listWithBadInterval, xs => {
        expect(() => mergeIntervals(xs)).toThrow(RangeError);
      }),
    );
  });

  // Example (not a property): the spec says [] gives [].
  it('[] gives []', () => {
    expect(mergeIntervals([])).toEqual([]);
  });
});
