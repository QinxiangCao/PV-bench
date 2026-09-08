/*@ Extern Coq
      (EnergyValsDuplicated : list Z -> list Z -> Z -> Prop)
      (EnergyLabelsBounded : list Z -> Z -> Prop)
      (EnergyComputationBounded : list Z -> Z -> Z -> Prop)
      (EnergyNecklaceAnswer : list Z -> Z -> Z -> Prop)
      (EnergyLenDone : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.energy_necklace.rocq.spec_lib */

int energyNecklace(int *beads, int n, int *vals, int *dp)
/*@ With (beads_l : list Z)
    Require
      4 <= n && n <= 100 &&
      Zlength(beads_l) == n &&
      EnergyLabelsBounded(beads_l, n) &&
      EnergyComputationBounded(beads_l, n, 2100000000) &&
      IntArray::full(beads, n, beads_l) *
      IntArray::undef_full(vals, 2 * n) *
      IntArray::undef_full(dp, (2 * n) * (2 * n))
    Ensure
      exists vals_l dp_l,
      EnergyValsDuplicated(beads_l, vals_l, n) &&
      EnergyLenDone(vals_l, dp_l, 2 * n, 2 * n, n + 1) &&
      EnergyNecklaceAnswer(beads_l, n, __return) &&
      0 <= __return && __return <= 2100000000 &&
      IntArray::full(beads, n, beads_l) *
      IntArray::full(vals, 2 * n, vals_l) *
      IntArray::full(dp, (2 * n) * (2 * n), dp_l)
 */
{
  int total = 2 * n;
  int width = total;

  for (int i = 0; i < n; ++i) {
    vals[i] = beads[i];
  }

  for (int i = 0; i < n; ++i) {
    vals[n + i] = beads[i];
  }

  for (int i = 0; i < total * width; ++i) {
    dp[i] = 0;
  }

  for (int len = 2; len <= n; ++len) {

    for (int left = 0; left < total - len; ++left) {
      int right = left + len - 1;
      int best = 0;

      for (int split = left; split < right; ++split) {

        int left_value = dp[left * width + split];
        int right_value = dp[(split + 1) * width + right];
        int gain = vals[left] * vals[split + 1] * vals[right + 1];
        int candidate = left_value + right_value + gain;

        if (candidate > best) {
          best = candidate;
        }

      }

      dp[left * width + right] = best;

    }

  }

  int answer = 0;

  for (int start = 0; start < n; ++start) {

    int value = dp[start * width + start + n - 1];

    if (value > answer) {
      answer = value;
    }

  }

  return answer;
}
