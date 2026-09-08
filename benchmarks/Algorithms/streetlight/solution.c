int solve(int *pos, int *power, int n, int c,
          int *pre, int *dp_l, int *dp_r)

{
  int width = n;
  int inf = 2147483647;
  int start = c - 1;

  pre[0] = 0;

  for (int i = 0; i < n; ++i) {
    pre[i + 1] = pre[i] + power[i];
  }
  int total = pre[n];

  for (int row = 0; row < n; ++row) {

    for (int col = 0; col < n; ++col) {
      *(dp_l + row * width + col) = inf;
      *(dp_r + row * width + col) = inf;
    }
  }

  *(dp_l + start * width + start) = 0;
  *(dp_r + start * width + start) = 0;

  for (int len = 2; len <= n; ++len) {
    int first_left = start - len + 1;
    if (first_left < 0) {
      first_left = 0;
    }

    int last_left = start;
    if (last_left + len > n) {
      last_left = n - len;
    }

    for (int left = first_left; left <= last_left; ++left) {
      int right = left + len - 1;

      if (left < start) {
        int remain = total - (pre[right + 1] - pre[left + 1]);

        int best = inf;
        int prev = *(dp_l + (left + 1) * width + right);

        if (prev < inf) {

          best = prev + (pos[left + 1] - pos[left]) * remain;

        }

        prev = *(dp_r + (left + 1) * width + right);
        if (prev < inf) {

          int cand = prev + (pos[right] - pos[left]) * remain;

          if (cand < best) {
            best = cand;
          }
        }

        *(dp_l + left * width + right) = best;
      }

      if (right > start) {
        int remain = total - (pre[right] - pre[left]);

        int best = inf;
        int prev = *(dp_l + left * width + (right - 1));

        if (prev < inf) {

          best = prev + (pos[right] - pos[left]) * remain;

        }

        prev = *(dp_r + left * width + (right - 1));
        if (prev < inf) {

          int cand = prev + (pos[right] - pos[right - 1]) * remain;

          if (cand < best) {
            best = cand;
          }
        }

        *(dp_r + left * width + right) = best;
      }
    }
  }

  int ans_l = *(dp_l + 0 * width + (n - 1));
  int ans_r = *(dp_r + 0 * width + (n - 1));

  if (ans_l < ans_r) {
    return ans_l;
  }
  return ans_r;
}
