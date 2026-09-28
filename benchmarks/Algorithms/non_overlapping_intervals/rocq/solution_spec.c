/*@ Extern Coq (interval :: *) */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::lt : Z -> Z -> Prop)
      (PairIntervals : list Z -> list Z -> list interval -> Prop)
      (MinimumRemovals : list interval -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.non_overlapping_intervals.rocq.spec_lib */

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
      swap_intervals(st, ed, i, j);
    }
  }

  swap_intervals(st, ed, i + 1, high);
  return i + 1;
}

void quicksort_intervals_range(int *st, int *ed, int intervalsSize,
                               int left, int right)

{
  if (left < right) {
    int pivot = partition_intervals(st, ed, intervalsSize, left, right);

    if (pivot > left) {
      quicksort_intervals_range(st, ed, intervalsSize, left, pivot - 1);
    }

    if (pivot < right) {
      quicksort_intervals_range(st, ed, intervalsSize, pivot + 1, right);
    }
  }
}

void quicksort_intervals(int *st, int *ed, int intervalsSize)

{
  quicksort_intervals_range(st, ed, intervalsSize, 0, intervalsSize - 1);
}

int eraseOverlapIntervals(int *st, int *ed, int intervalsSize)
/*@ With st_l ed_l ps
    Require
      0 <= intervalsSize && intervalsSize <= 1000 &&
      PairIntervals(st_l, ed_l, ps) &&
      Forall(Z::le(-10000), st_l) &&
      Forall2(Z::lt, st_l, ed_l) &&
      Forall(Z::ge(10000), ed_l) &&
      IntArray::full(st, intervalsSize, st_l) *
      IntArray::full(ed, intervalsSize, ed_l)
    Ensure
      MinimumRemovals(ps, __return) &&
      exists st1 ed1,
        IntArray::full(st, intervalsSize, st1) *
        IntArray::full(ed, intervalsSize, ed1)
*/
{
  quicksort_intervals(st, ed, intervalsSize);

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
