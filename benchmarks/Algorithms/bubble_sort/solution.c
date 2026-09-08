int* sortArray(int* nums, int numsSize, int* returnSize) 

{
    *returnSize = numsSize;
    if (numsSize <= 1) {
        return nums;
    }

    for (int i = 0; i < numsSize - 1; ++i) {

        for (int j = 0; j + 1 < numsSize - i; ++j) {
            if (nums[j] > nums[j + 1]) {
                int tmp = nums[j];
                nums[j] = nums[j + 1];
                nums[j + 1] = tmp;
            }
        }
    }
    return nums;
}