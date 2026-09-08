/*@ Extern Coq
      (LCSNTableResult : list Z -> list Z -> Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.lcs_n.rocq.spec_lib */

int lcs_n(int *x, int *y, int n, int *table)
/*@ With (xs ys : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(xs) == n && Zlength(ys) == n &&
      IntArray::full(x, n, xs) *
      IntArray::full(y, n, ys) *
      IntArray::undef_full(table, (n + 1) * (n + 1))
    Ensure
      exists table_l,
      LCSNTableResult(xs, ys, n, table_l) &&
      __return == Znth((n + 1) * n + n, table_l, 0) &&
      IntArray::full(x, n, xs) *
      IntArray::full(y, n, ys) *
      IntArray::full(table, (n + 1) * (n + 1), table_l)
 */
{
  int stride;
  int i;
  int j;
  int above;
  int left;

  stride = n + 1;

  i = 0;

  while (i <= n) {

    table[stride * i] = 0;
    i = i + 1;
  }

  j = 1;

  while (j <= n) {

    table[j] = 0;
    j = j + 1;
  }

  i = 1;

  while (i <= n) {
    j = 1;

    while (j <= n) {

      if (x[i - 1] == y[j - 1]) {

        table[stride * i + j] =
            table[stride * (i - 1) + (j - 1)] + 1;
      } else {

        above = table[stride * (i - 1) + j];
        left = table[stride * i + (j - 1)];
        if (above >= left) {
          table[stride * i + j] = above;
        } else {
          table[stride * i + j] = left;
        }
      }

      j = j + 1;
    }
    i = i + 1;
  }

  return table[stride * n + n];
}
