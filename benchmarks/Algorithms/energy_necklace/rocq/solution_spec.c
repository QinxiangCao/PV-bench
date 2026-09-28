/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (EnergyValsDuplicated : list Z -> list Z -> Z -> Prop)
      (EnergyIntervalPlan : list Z -> Z -> Z -> Z -> Prop)
      (EnergyNecklaceAnswer : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.energy_necklace.rocq.spec_lib */

int energyNecklace(int *beads, int n)
/*@ With (beads_l : list Z)
    Require
      4 <= n && n <= 100 &&
      Zlength(beads_l) == n &&
      Zlength(beads_l) == n && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
      (forall (ev : list Z) (start : Z) (energy : Z),
        (EnergyValsDuplicated(beads_l, ev, n) &&
         0 <= start && start < n &&
         EnergyIntervalPlan(ev, start, start + n - 1, energy)) =>
        energy <= 2100000000) &&
      IntArray::full(beads, n, beads_l)
    Ensure
      EnergyNecklaceAnswer(beads_l, n, __return) &&
      IntArray::full(beads, n, beads_l)
 */
{
  int vals[200];
  int dp[40000];

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

  int result = answer;

  return result;
}
