int rob(int *nums, int n)

{
  int prev2 = 0;
  int prev1 = 0;

  for (int i = 0; i < n; ++i) {
    int take = prev2 + nums[i];
    int skip = prev1;
    int cur;
    if (take > skip) {
      cur = take;
    } else {
      cur = skip;
    }
    prev2 = prev1;
    prev1 = cur;
  }
  return prev1;
}
