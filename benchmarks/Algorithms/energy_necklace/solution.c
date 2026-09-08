int energyNecklace(int *beads, int n, int *vals, int *dp)

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
