#include "array2_def.h"

/*@ Extern Coq
      (StoneMassesBounded : list Z -> Z -> Prop)
      (StoneMinimumCost : list Z -> Z -> Z -> Prop)
      (StonePrefixDone : list Z -> list Z -> Z -> Prop)
      (StoneTableShape : list (list Z) -> Z -> Prop)
      (StoneLenDone : list Z -> list (list Z) -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.merging_stones.rocq.spec_lib */

/*
 * Minimum cost of merging adjacent stone piles by interval dynamic
 * programming.  The verified range is deliberately limited to n <= 8.
 */
int mergingStones(int *stones, int n, int *prefix, int *dp)
/*@ With (stones_l : list Z) (dp_init : list (list Z))
    Require
      1 <= n && n <= 8 &&
      Zlength(stones_l) == n &&
      StoneMassesBounded(stones_l, n) &&
      StoneTableShape(dp_init, n) &&
      IntArray::full(stones, n, stones_l) *
      IntArray::undef_full(prefix, n + 1) *
      IntArray2::full(dp, n, n, dp_init)
    Ensure
      exists prefix_l dp_l,
      StonePrefixDone(stones_l, prefix_l, n) &&
      StoneLenDone(stones_l, dp_l, n, n + 1) &&
      StoneMinimumCost(stones_l, n, __return) &&
      0 <= __return && __return <= 56000 &&
      IntArray::full(stones, n, stones_l) *
      IntArray::full(prefix, n + 1, prefix_l) *
      IntArray2::full(dp, n, n, dp_l)
 */
{
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

  return *(dp + 0 * width + (n - 1));
}
