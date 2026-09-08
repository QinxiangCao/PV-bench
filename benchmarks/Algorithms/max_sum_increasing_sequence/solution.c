int maxSumIncreasingSequence(int *nums, int numsSize, int *dp)

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
