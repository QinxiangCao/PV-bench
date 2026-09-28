/*@ Extern Coq
      (minister :: *)
 */
/*@ Extern Coq
      (minister_left : minister -> Z)
      (minister_right : minister -> Z)
      (FlatMinisters : list Z -> list minister -> Prop)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (KingsGameResult : list minister -> Z -> list minister -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.kings_game.rocq.spec_lib */

void swap_ministers(int *a, int n, int i, int j)

{
  int tmp_left = a[2 * i];
  int tmp_right = a[2 * i + 1];
  a[2 * i] = a[2 * j];
  a[2 * i + 1] = a[2 * j + 1];
  a[2 * j] = tmp_left;
  a[2 * j + 1] = tmp_right;
}

void kings_game(int *ministers, int n, int king_left, int king_right, int *ans)
/*@ With (input_flat : list Z) (input : list minister)
    Require
      1 <= n && n <= 8 &&
      1 <= king_left && king_left <= 10 &&
      1 <= king_right && king_right <= 10 &&
      Zlength(input) == n &&
      FlatMinisters(input_flat, input) &&
      Forall(Z::le(1), map(minister_left, input)) &&
      Forall(Z::ge(10), map(minister_left, input)) &&
      Forall(Z::le(1), map(minister_right, input)) &&
      Forall(Z::ge(10), map(minister_right, input)) &&
      IntArray::full(ministers, 2 * n, input_flat) *
      IntArray::undef_full(ans, 2 * n)
    Ensure
      exists output_flat output,
        FlatMinisters(output_flat, output) &&
        KingsGameResult(input, king_left, output) &&
        IntArray::full(ministers, 2 * n, input_flat) *
        IntArray::full(ans, 2 * n, output_flat)
 */
{
  (void)king_right;

  for (int k = 0; k < 2 * n; k++) {
    ans[k] = ministers[k];
  }

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
