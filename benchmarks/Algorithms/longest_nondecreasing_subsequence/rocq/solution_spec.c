/*@ Extern Coq
      (LNDSLength : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.longest_nondecreasing_subsequence.rocq.spec_lib */

int lengthOfLNDS(int *nums, int numsSize, int *tails)
/*@ With (l : list Z) (tails_l : list Z)
    Require
      0 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      Zlength(tails_l) == numsSize &&
      IntArray::full(nums, numsSize, l) *
      IntArray::full(tails, numsSize, tails_l)
    Ensure
      exists tails_ret,
      LNDSLength(l, __return) &&
      0 <= __return && __return <= numsSize &&
      Zlength(tails_ret) == numsSize &&
      IntArray::full(nums, numsSize, l) *
      IntArray::full(tails, numsSize, tails_ret)
 */
{
  int len = 0;

  for (int i = 0; i < numsSize; ++i) {
    int x = nums[i];

    int left = 0;
    int right = len;

    while (left < right) {
      int mid = left + (right - left) / 2;

      if (tails[mid] <= x) {
        left = mid + 1;
      } else {
        right = mid;
      }
    }

    tails[left] = x;

    if (left == len) {
      len = len + 1;
    }

  }

  return len;
}
