int zeroOneKnapsack(int *weights, int *values, int n, int capacity, int *dp)

{
  int width = capacity + 1;

  for (int i = 0; i <= n; ++i) {

    for (int j = 0; j <= capacity; ++j) {
      int idx = i * width + j;

      if (i == 0) {
        dp[idx] = 0;
      } else if (j == 0) {
        dp[idx] = 0;
      } else {
        int item = i - 1;

        int w = weights[item];
        int v = values[item];

        int without = dp[(i - 1) * width + j];

        if (w <= j) {

          int prev = dp[(i - 1) * width + (j - w)];
          int with_val = prev + v;
          if (with_val > without) {
            dp[idx] = with_val;
          } else {
            dp[idx] = without;
          }
        } else {
          dp[idx] = without;
        }
      }
    }
  }

  return dp[n * width + capacity];
}
