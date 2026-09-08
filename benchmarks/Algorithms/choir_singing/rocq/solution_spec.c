/*@ Extern Coq
      (ChoirDPLeftPrefix : list Z -> list Z -> Z -> Prop)
      (ChoirDPRightSuffix : list Z -> list Z -> Z -> Prop)
      (ChoirMinimumRemovals : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.choir_singing.rocq.spec_lib */

int choir_singing(int *nums, int numsSize, int *dp_left, int *dp_right)
/*@ With (heights : list Z)
    Require
      1 <= numsSize && numsSize <= 100 &&
      Zlength(heights) == numsSize &&
      IntArray::full(nums, numsSize, heights) *
      IntArray::undef_full(dp_left, numsSize) *
      IntArray::undef_full(dp_right, numsSize)
    Ensure
      exists left_values right_values,
      ChoirMinimumRemovals(heights, __return) &&
      0 <= __return && __return < numsSize &&
      ChoirDPLeftPrefix(heights, left_values, numsSize) &&
      ChoirDPRightSuffix(heights, right_values, 0) &&
      IntArray::full(nums, numsSize, heights) *
      IntArray::full(dp_left, numsSize, left_values) *
      IntArray::full(dp_right, numsSize, right_values)
 */
{

  for (int i = 0; i < numsSize; ++i) {
    dp_left[i] = 1;
    dp_right[i] = 1;
  }

  for (int i = 0; i < numsSize; ++i) {

    for (int j = i - 1; j >= 0; --j) {
      if (nums[j] < nums[i] && dp_left[j] + 1 > dp_left[i]) {
        dp_left[i] = dp_left[j] + 1;
      }
    }

  }

  for (int i = numsSize - 1; i >= 0; --i) {

    for (int j = i + 1; j < numsSize; ++j) {
      if (nums[j] < nums[i] && dp_right[j] + 1 > dp_right[i]) {
        dp_right[i] = dp_right[j] + 1;
      }
    }

  }

  int max_choir = 0;

  for (int k = 0; k < numsSize; ++k) {
    if (dp_left[k] + dp_right[k] > max_choir) {
      max_choir = dp_left[k] + dp_right[k] - 1;
    }
  }

  return numsSize - max_choir;
}
