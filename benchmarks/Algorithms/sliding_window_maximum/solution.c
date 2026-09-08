void maxSlidingWindow(int *nums, int n, int k, int *out, int *q)

{
  int head = 0;
  int tail = 0;
  int out_idx = 0;

  for (int i = 0; i < n; ++i) {

    while (head < tail && q[head] <= i - k) {
      head++;
    }

    while (head < tail && nums[q[tail - 1]] <= nums[i]) {
      tail--;
    }

    q[tail] = i;
    tail++;

    if (i >= k - 1) {

      out[out_idx] = nums[q[head]];

      out_idx++;
    }

  }

}
