/*
 * Minimum cost of merging adjacent stone piles by interval dynamic
 * programming.  The verified range is deliberately limited to n <= 8.
 */
int mergingStones(int *stones, int n, int *prefix, int *dp)

{
  int width = n;

  prefix[0] = 0;

  for (int i = 0; i < n; ++i) {

    prefix[i + 1] = prefix[i] + stones[i];
  }

  for (int row = 0; row < n; ++row) {

    for (int col = 0; col < n; ++col) {
      *(dp + row * width + col) = 0;
    }

  }

  for (int len = 2; len <= n; ++len) {

    for (int left = 0; left + len <= n; ++left) {
      int right = left + len - 1;
      int interval_sum = prefix[right + 1] - prefix[left];
      int best = 1000000;

      for (int split = left; split < right; ++split) {

        int left_value = *(dp + left * width + split);

        int right_value = *(dp + (split + 1) * width + right);
        int candidate = left_value + right_value + interval_sum;

        if (candidate < best) {
          best = candidate;
        }

      }

      *(dp + left * width + right) = best;

    }

  }

  return *(dp + 0 * width + (n - 1));
}
