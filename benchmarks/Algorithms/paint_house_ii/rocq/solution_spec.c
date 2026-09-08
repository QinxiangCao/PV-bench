#include "int_ptr_array2_def.h"

/*@ Extern Coq
      (PaintHouseIIAnswer : list (list Z) -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.paint_house_ii.rocq.spec_lib */

int paint_house_ii(int **costs, int n, int k)
/*@ With (costs_l : list (list Z))
    Require
      1 <= n && n <= 10000 &&
      2 <= k && k <= 1000 &&
      n * k <= 1000000 &&
      Zlength(costs_l) == n &&
      (forall (r : Z), (0 <= r && r < n) => (Zlength(costs_l[r]) == k)) &&
      (forall (r : Z) (c : Z),
        (0 <= r && r < n && 0 <= c && c < k) => (0 <= costs_l[r][c] && costs_l[r][c] <= 10000)) &&
      IntPtrArray2::full(costs, n, costs_l)
    Ensure
      PaintHouseIIAnswer(costs_l, n, k, __return) &&
      0 <= __return && __return <= 1000000000 &&
      IntPtrArray2::full(costs, n, costs_l)
 */
{
  int min1 = 0;
  int min2 = 0;
  int min1_color = -1;

  for (int i = 0; i < n; ++i) {
    int new_min1 = 1000000000;
    int new_min2 = 1000000000;
    int new_min1_color = -1;

    for (int c = 0; c < k; ++c) {
      int prev;
      if (c == min1_color) {
        prev = min2;
      } else {
        prev = min1;
      }

      int total = prev + costs[i][c];

      if (total < new_min1) {
        new_min2 = new_min1;
        new_min1 = total;
        new_min1_color = c;
      } else {
        if (total < new_min2) {
          new_min2 = total;
        }
      }

    }

    min1 = new_min1;
    min2 = new_min2;
    min1_color = new_min1_color;

  }

  return min1;
}
