#include "array2_def.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (StoneMinimumCost : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.merging_stones.rocq.spec_lib */

int mergingStones(int *stones, int n)
/*@ With (stones_l : list Z) 
    Require
      1 <= n && n <= 8 &&
      Zlength(stones_l) == n &&
      Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
      IntArray::full(stones, n, stones_l)
    Ensure
      StoneMinimumCost(stones_l, __return) &&
      IntArray::full(stones, n, stones_l)
 */
{
  int prefix[9];
  int dp[64];

  for (int k = 0; k < n * n; ++k) {
    dp[k] = 0;
  }

  int width = n;
  prefix[0] = 0;

  for (int i = 0; i < n; ++i) {
    prefix[i + 1] = prefix[i] + stones[i];
  }

  for (int row = 0; row < n; ++row) {

    for (int col = 0; col < n; ++col) {
      *(dp + row * width + col) = 0;
    }
  }

  for (int len = 2; len <= n; ++len) {

    for (int left = 0; left + len <= n; ++left) {
      int right = left + len - 1;
      int interval_sum = prefix[right + 1] - prefix[left];
      int best = 1000000;

      for (int split = left; split < right; ++split) {
        int left_value = *(dp + left * width + split);

        int right_value = *(dp + (split + 1) * width + right);
        int candidate = left_value + right_value + interval_sum;
        if (candidate < best) {
          best = candidate;
        }
      }
      *(dp + left * width + right) = best;
    }
  }
  int result = *(dp + 0 * width + (n - 1));

  return result;
}
