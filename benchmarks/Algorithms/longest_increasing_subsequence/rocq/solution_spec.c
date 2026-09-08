/*@ Extern Coq
      (LISLength : list Z -> Z -> Prop)
      (LISDPTablePrefix : list Z -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.longest_increasing_subsequence.rocq.spec_lib */

int lengthOfLIS(int *nums, int numsSize, int *dp)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      IntArray::full(nums, numsSize, l) *
      IntArray::undef_full(dp, numsSize)
    Ensure
      exists d,
      LISLength(l, __return) &&
      1 <= __return && __return <= numsSize &&
      LISDPTablePrefix(l, d, numsSize) &&
      IntArray::full(nums, numsSize, l) *
      IntArray::full(dp, numsSize, d)
 */
{
  int ans = 1;

  for (int i = 0; i < numsSize; ++i) {
    dp[i] = 1;

    for (int j = 0; j < i; ++j) {
      if (nums[j] < nums[i]) {
        int candidate = dp[j] + 1;
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
