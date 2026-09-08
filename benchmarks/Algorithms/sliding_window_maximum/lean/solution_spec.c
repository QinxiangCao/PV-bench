/*@ Import Lean
import Algorithms.sliding_window_maximum.lean.spec_lib
open scoped SimpleC
*/
/*@ Extern Coq
      (SWMInputSafe : list Z -> Z -> Z -> Prop)
	      (SlidingWindowMaximum : list Z -> Z -> list Z -> Prop)
 */

void maxSlidingWindow(int *nums, int n, int k, int *out, int *q)
/*@ With (l : list Z) (q0 : list Z)
    Require
      1 <= k && k <= n && n <= 100000 &&
      Zlength(l) == n &&
      Zlength(q0) == n &&
      SWMInputSafe(l, n, k) &&
      IntArray::full(nums, n, l) *
      IntArray::undef_full(out, n - k + 1) *
      IntArray::full(q, n, q0)
    Ensure
      exists out_l q_l,
      SlidingWindowMaximum(l, k, out_l) &&
      IntArray::full(nums, n, l) *
      IntArray::full(out, n - k + 1, out_l) *
      IntArray::full(q, n, q_l)
 */
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
