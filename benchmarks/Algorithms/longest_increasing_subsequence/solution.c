int lengthOfLIS(int *nums, int numsSize)

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
