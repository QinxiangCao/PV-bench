int lengthOfLNDS(int *nums, int numsSize, int *tails)

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
