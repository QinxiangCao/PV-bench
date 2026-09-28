/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
 */
/*@ Extern Coq
      (increasing : list Z -> Prop)
 */

/*@ Import Coq Require Import PVbench.Algorithms.bubble_sort.rocq.spec_lib */

int* sortArray(int* nums, int numsSize, int* returnSize) 
/*@ With (l: list Z)
    Require Zlength(l) == numsSize && 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l) * has_int_permission(returnSize)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && IntArray::full(__return, numsSize, l1) && *returnSize == numsSize
*/
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
