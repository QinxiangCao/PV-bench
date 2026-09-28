/*@ Extern Coq
      (LNDSLength : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.longest_nondecreasing_subsequence.rocq.spec_lib */

int lengthOfLNDS(int *nums, int numsSize)
/*@ With (l : list Z)
    Require
      0 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      IntArray::full(nums, numsSize, l)
    Ensure
      LNDSLength(l, __return) &&
      IntArray::full(nums, numsSize, l)
 */
{
  int tails[100000];

  for (int fill = 0; fill < numsSize; ++fill) {
    tails[fill] = 0;
  }

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
