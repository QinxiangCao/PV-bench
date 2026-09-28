/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (LISLength : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.longest_increasing_subsequence.rocq.spec_lib */

int lengthOfLIS(int *nums, int numsSize)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, numsSize, l)
    Ensure
      LISLength(l, __return) &&
      IntArray::full(nums, numsSize, l)
 */
{
  int dp[100000];

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
