/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (MSISMaximum : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.max_sum_increasing_sequence.rocq.spec_lib */

int maxSumIncreasingSequence(int *nums, int numsSize)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      Forall(Z::le(1), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, numsSize, l)
    Ensure
      MSISMaximum(l, __return) &&
      IntArray::full(nums, numsSize, l)
 */
{
  int dp[100000];

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
