/*@ Import Lean
import Algorithms.zero_one_knapsack.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq
      (KnapsackInputsBounded : list Z -> list Z -> Z -> Z -> Prop)
      (KnapsackResultState : list Z -> list Z -> Z -> Z -> list Z -> Z -> Prop)
 */
int zeroOneKnapsack(int *weights, int *values, int n, int capacity, int *dp)
/*@ With (weights_l values_l : list Z)
    Require
      0 <= n && n <= 300 &&
      0 <= capacity && capacity <= 300 &&
      KnapsackInputsBounded(weights_l, values_l, n, capacity) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::undef_full(dp, (n + 1) * (capacity + 1))
    Ensure
      exists dp_l,
      KnapsackResultState(weights_l, values_l, n, capacity, dp_l, __return) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(dp, (n + 1) * (capacity + 1), dp_l)
 */
{
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

  return dp[n * width + capacity];
}
