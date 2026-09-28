#include "int_ptr_array2_def.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (eq : {A} -> A -> A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (PaintHouseIIOptimalCost : list (list Z) -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.paint_house_ii.rocq.spec_lib */

int paint_house_ii(int **costs, int n, int k)
/*@ With (costs_l : list (list Z))
    Require
      1 <= n && n <= 10000 &&
      2 <= k && k <= 1000 &&
      n * k <= 1000000 &&
      Zlength(costs_l) == n &&
      Forall(eq(k), map(Zlength, costs_l)) &&
      Forall(Forall(Z::le(0)), costs_l) && Forall(Forall(Z::ge(10000)), costs_l) &&
      IntPtrArray2::full(costs, n, costs_l)
    Ensure
      PaintHouseIIOptimalCost(costs_l, n, k, __return) &&
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
