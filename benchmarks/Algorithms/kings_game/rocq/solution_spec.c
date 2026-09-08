/*@ Extern Coq
      (FlatMinisters : list Z -> list minister -> Prop)
      (MinisterHandsBound : list minister -> Prop)
      (KingsGameResult : list minister -> Z -> list minister -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.kings_game.rocq.spec_lib */

/* Swap two complete flat minister records. */
void swap_ministers(int *a, int n, int i, int j)

{
  int tmp_left = a[2 * i];
  int tmp_right = a[2 * i + 1];
  a[2 * i] = a[2 * j];
  a[2 * i + 1] = a[2 * j + 1];
  a[2 * j] = tmp_left;
  a[2 * j + 1] = tmp_right;
}

/*
 * This verification-oriented implementation deliberately uses the bounded
 * domain 1 <= n <= 8 and hand values in [1,10].  Thus every comparison key is
 * at most 100 and king_left times all minister left hands is at most 10^9;
 * ordinary signed int arithmetic is sufficient and no high-precision code is
 * used.
 *
 * The strict comparison makes the adjacent-swap bubble sort stable for equal
 * left*right keys.  The formal result is stronger than sortedness: it says the
 * produced permutation realises the MaxMinLib minimax reward specification.
 */
void kings_game(int *ministers, int n, int king_left, int king_right, int *ans)
/*@ With (input_flat : list Z) (input : list minister)
    Require
      1 <= n && n <= 8 &&
      1 <= king_left && king_left <= 10 &&
      1 <= king_right && king_right <= 10 &&
      Zlength(input) == n &&
      FlatMinisters(input_flat, input) &&
      MinisterHandsBound(input) &&
      IntArray::full(ministers, 2 * n, input_flat) *
      IntArray::undef_full(ans, 2 * n)
    Ensure
      exists output_flat output,
        Zlength(output) == n &&
        FlatMinisters(output_flat, output) &&
        MinisterHandsBound(output) &&
        KingsGameResult(input, king_left, output) &&
        IntArray::full(ministers, 2 * n, input_flat) *
        IntArray::full(ans, 2 * n, output_flat)
 */
{
  (void)king_right;

  /* First copy the complete flat input, preserving the disjoint source. */

  for (int k = 0; k < 2 * n; k++) {
    ans[k] = ministers[k];
  }

  /* Bubble the largest remaining key into the next suffix position. */

  for (int pass = 0; pass < n - 1; pass++) {

    for (int j = 0; j < n - 1 - pass; j++) {
      int left1 = ans[2 * j];
      int right1 = ans[2 * j + 1];
      int left2 = ans[2 * (j + 1)];
      int right2 = ans[2 * (j + 1) + 1];

      if (left1 * right1 > left2 * right2) {
        swap_ministers(ans, n, j, j + 1) ;
      }
    }
  }
}
