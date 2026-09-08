int choir_singing(int *nums, int numsSize, int *dp_left, int *dp_right)

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
