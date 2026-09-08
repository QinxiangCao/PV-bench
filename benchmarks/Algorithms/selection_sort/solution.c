void sortArray(int* nums, int numsSize) 

{

    for (int i = 0; i < numsSize; ++i) {

        for (int j = i + 1; j < numsSize; ++j) {
            if (nums[j] < nums[i]) {
                int tmp = nums[i];
                nums[i] = nums[j];
                nums[j] = tmp;
            }
        }
    }
    return ;
}
