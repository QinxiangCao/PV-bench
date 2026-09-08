/*@ Import Lean
import Algorithms.non_overlapping_intervals.lean.spec_lib
open scoped SimpleC
*/

/*
 * LeetCode 435: Non-overlapping Intervals.
 *
 * The two arrays st and ed represent the interval records in parallel:
 * interval i is [st[i], ed[i]].  Quicksort always swaps both fields of a
 * record, then the earliest-finish-time scan computes a maximum-cardinality
 * compatible subset.  Therefore intervalsSize - kept is the minimum number
 * of removals.
 */

/*@ Extern Coq (interval :: *) */
/*@ Extern Coq
      (PairIntervals : list Z -> list Z -> list interval -> Prop)
      (IntervalBounds : list interval -> Prop)
      (IntervalPermutation : list interval -> list interval -> Prop)
      (IntervalsEndSorted : list interval -> Prop)
      (MinimumRemovals : list interval -> Z -> Prop)
 */
void swap_intervals(int *st, int *ed, int i, int j)

{
  int start = st[i];
  int end = ed[i];
  st[i] = st[j];
  ed[i] = ed[j];
  st[j] = start;
  ed[j] = end;
}

int partition_intervals(int *st, int *ed, int intervalsSize,
                        int low, int high)

{
  int pivot_end = ed[high];
  int i = low - 1;

  for (int j = low; j < high; ++j) {

    if (ed[j] <= pivot_end) {
      ++i;
      swap_intervals(st, ed, i, j) ;
    }
  }

  swap_intervals(st, ed, i + 1, high) ;
  return i + 1;
}

void quicksort_intervals_range(int *st, int *ed, int intervalsSize,
                               int left, int right)

{
  if (left < right) {
    int pivot = partition_intervals(st, ed, intervalsSize, left, right)
      ;

    if (pivot > left) {
      quicksort_intervals_range(st, ed, intervalsSize, left, pivot - 1)
        ;
    }

    if (pivot < right) {
      quicksort_intervals_range(st, ed, intervalsSize, pivot + 1, right)
        ;
    }
  }
}

void quicksort_intervals(int *st, int *ed, int intervalsSize)

{
  quicksort_intervals_range(st, ed, intervalsSize, 0, intervalsSize - 1)
    ;
}

int eraseOverlapIntervals(int *st, int *ed, int intervalsSize)
/*@ With st_l ed_l ps
    Require
      0 <= intervalsSize && intervalsSize <= 1000 &&
      PairIntervals(st_l, ed_l, ps) &&
      IntervalBounds(ps) &&
      IntArray::full(st, intervalsSize, st_l) *
      IntArray::full(ed, intervalsSize, ed_l)
    Ensure
      0 <= __return && __return <= intervalsSize &&
      MinimumRemovals(ps, __return) &&
      exists st1 ed1 ps1,
        PairIntervals(st1, ed1, ps1) &&
        IntervalBounds(ps1) &&
        IntervalPermutation(ps, ps1) &&
        IntervalsEndSorted(ps1) &&
        IntArray::full(st, intervalsSize, st1) *
        IntArray::full(ed, intervalsSize, ed1)
*/
{
  quicksort_intervals(st, ed, intervalsSize) ;

  if (intervalsSize == 0) {
    return 0;
  }

  int kept = 1;
  int last_end = ed[0];

  for (int i = 1; i < intervalsSize; ++i) {
    if (st[i] >= last_end) {
      ++kept;
      last_end = ed[i];
    }
  }

  return intervalsSize - kept;
}
