/*@ Extern Coq
      (MSISMaximum : list Z -> Z -> Prop)
      (MSISDPTablePrefix : list Z -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.max_sum_increasing_sequence.rocq.spec_lib */

int maxSumIncreasingSequence(int *nums, int numsSize, int *dp)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      (forall (k : Z),
        (0 <= k && k < numsSize) =>
        (1 <= l[k] && l[k] <= 10000)) &&
      IntArray::full(nums, numsSize, l) *
      IntArray::undef_full(dp, numsSize)
    Ensure
      exists d,
      MSISMaximum(l, __return) &&
      1 <= __return && __return <= INT_MAX &&
      MSISDPTablePrefix(l, d, numsSize) &&
      IntArray::full(nums, numsSize, l) *
      IntArray::full(dp, numsSize, d)
 */
{
  dp[0] = nums[0];
  int ans = nums[0];

  for (int i = 1; i < numsSize; ++i) {
    dp[i] = nums[i];

    for (int j = 0; j < i; ++j) {
      if (nums[j] < nums[i]) {
        int candidate = dp[j] + nums[i];
        if (candidate > dp[i]) {
          dp[i] = candidate;
        }
      }
    }

    if (dp[i] > ans) {
      ans = dp[i];
    }
  }
  return ans;
}
