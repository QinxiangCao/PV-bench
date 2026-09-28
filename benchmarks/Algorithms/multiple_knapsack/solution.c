int multipleKnapsack(int *weights, int *values, int *counts,
                     int n, int capacity)

{
  int dp[1001];
  int old[1001];
  int q_idx[1001];
  int q_val[1001];

  for (int j = 0; j <= capacity; ++j) {
    dp[j] = 0;
    old[j] = 0;
    q_idx[j] = 0;
    q_val[j] = 0;
  }

  for (int i = 0; i < n; ++i) {

    for (int j = 0; j <= capacity; ++j) {
      old[j] = dp[j];
    }

    int w = weights[i];
    int v = values[i];
    int cnt = counts[i];

    for (int r = 0; r < w && r <= capacity; ++r) {
      int head = 0;
      int tail = 0;
      int k = 0;

      for (int pos = r; pos <= capacity; pos += w) {
        int current = old[pos] - k * v;

        while (head < tail && q_idx[head] < k - cnt) {
          head++;
        }

        while (head < tail && q_val[tail - 1] <= current) {
          tail--;
        }

        q_idx[tail] = k;
        q_val[tail] = current;
        tail++;

        dp[pos] = q_val[head] + k * v;
        k++;
      }

    }

  }

  int answer = dp[capacity];

  return answer;
}
