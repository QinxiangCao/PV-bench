int majorityElement(int* nums, int numsSize)

{
    int vote = 0;
    int candidate = 0;

    for (int i = 0; i < numsSize; i++) {
        if (vote == 0) {
            candidate = nums[i];
        }
        vote += (nums[i] == candidate) ? 1 : -1;
    }
    return candidate;
}