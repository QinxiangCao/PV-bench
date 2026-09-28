/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (SlidingWindowMaximum : list Z -> Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.sliding_window_maximum.rocq.spec_lib */

void maxSlidingWindow(int *nums, int n, int k, int *out)
/*@ With (l : list Z)
    Require
      1 <= k && k <= n && n <= 100000 &&
      Zlength(l) == n &&
      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, n, l) *
      IntArray::undef_full(out, n - k + 1)
    Ensure
      exists out_l,
      SlidingWindowMaximum(l, k, out_l) &&
      IntArray::full(nums, n, l) *
      IntArray::full(out, n - k + 1, out_l)
 */
{
  int q[100000];

  for (int z = 0; z < n; ++z) {
    q[z] = 0;
  }

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
