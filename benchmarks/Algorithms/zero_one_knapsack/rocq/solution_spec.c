/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (KnapsackMaxValue : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.zero_one_knapsack.rocq.spec_lib */

int zeroOneKnapsack(int *weights, int *values, int n, int capacity)
/*@ With (weights_l values_l : list Z)
    Require
      0 <= n && n <= 300 &&
      0 <= capacity && capacity <= 300 &&
      Zlength(weights_l) == n && Zlength(values_l) == n &&
      Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity + 1), weights_l) &&
      Forall(Z::le(0), values_l) && Forall(Z::ge(10000), values_l) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l)
    Ensure
      KnapsackMaxValue(weights_l, values_l, n, capacity, __return) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l)
 */
{
  int dp[90601];

  int width = capacity + 1;

  for (int i = 0; i <= n; ++i) {

    for (int j = 0; j <= capacity; ++j) {
      int idx = i * width + j;

      if (i == 0) {
        dp[idx] = 0;
      } else if (j == 0) {
        dp[idx] = 0;
      } else {
        int item = i - 1;

        int w = weights[item];
        int v = values[item];

        int without = dp[(i - 1) * width + j];

        if (w <= j) {

          int prev = dp[(i - 1) * width + (j - w)];
          int with_val = prev + v;
          if (with_val > without) {
            dp[idx] = with_val;
          } else {
            dp[idx] = without;
          }
        } else {
          dp[idx] = without;
        }
      }
    }
  }

  int result = dp[n * width + capacity];

  return result;
}
