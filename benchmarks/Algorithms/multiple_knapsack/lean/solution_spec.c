/*@ Import Lean
import Algorithms.multiple_knapsack.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq
      (MultipleKnapsackAnswer : list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (MKScratchArraysSafety : list Z -> list Z -> list Z -> Z -> Prop)
      (MKDPTableSafety : list Z -> Z -> Z -> list Z -> Prop)
      (MKDPTableSemantics : list Z -> list Z -> list Z -> Z -> Z -> list Z -> Prop)
 */
int multipleKnapsack(int *weights, int *values, int *counts,
                     int n, int capacity,
                     int *dp, int *old, int *q_idx, int *q_val)
/*@ With (weights_l : list Z) (values_l : list Z) (counts_l : list Z)
          (old0 : list Z) (qidx0 : list Z) (qval0 : list Z)
    Require
      0 <= n && n <= 1000 &&
      0 <= capacity && capacity <= 1000 &&
      Zlength(weights_l) == n &&
      Zlength(values_l) == n &&
      Zlength(counts_l) == n &&
      MKScratchArraysSafety(old0, qidx0, qval0, capacity) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(counts, n, counts_l) *
      IntArray::undef_full(dp, capacity + 1) *
      IntArray::full(old, capacity + 1, old0) *
      IntArray::full(q_idx, capacity + 1, qidx0) *
      IntArray::full(q_val, capacity + 1, qval0) &&
      (forall (idx : Z), (0 <= idx && idx < n) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity))
    Ensure
      exists dp_l old_l qidx_l qval_l,
      MultipleKnapsackAnswer(weights_l, values_l, counts_l, capacity, __return) &&
      MKDPTableSafety(weights_l, n, capacity, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, n, capacity, dp_l) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(counts, n, counts_l) *
      IntArray::full(dp, capacity + 1, dp_l) *
      IntArray::full(old, capacity + 1, old_l) *
      IntArray::full(q_idx, capacity + 1, qidx_l) *
      IntArray::full(q_val, capacity + 1, qval_l)
 */
{

  for (int j = 0; j <= capacity; ++j) {
    dp[j] = 0;
  }

  for (int i = 0; i < n; ++i) {

    for (int j = 0; j <= capacity; ++j) {
      old[j] = dp[j];
    }

    int w = weights[i];
    int v = values[i];
    int cnt = counts[i];

    for (int r = 0; r < w && r <= capacity; ++r) {
      int head = 0;
      int tail = 0;
      int k = 0;

      for (int pos = r; pos <= capacity; pos += w) {
        int current = old[pos] - k * v;

        while (head < tail && q_idx[head] < k - cnt) {
          head++;
        }

        while (head < tail && q_val[tail - 1] <= current) {
          tail--;
        }

        q_idx[tail] = k;
        q_val[tail] = current;
        tail++;

        dp[pos] = q_val[head] + k * v;
        k++;
      }

    }

  }

  return dp[capacity];
}
