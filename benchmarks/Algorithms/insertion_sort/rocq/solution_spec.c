/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
 */
/*@ Extern Coq
      (increasing : list Z -> Prop)
 */

/*@ Import Coq Require Import PVbench.Algorithms.insertion_sort.rocq.spec_lib */

int* sortArray(int* nums, int numsSize, int* returnSize) 
/*@ With (l: list Z)
    Require Zlength(l) == numsSize && 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l) * has_int_permission(returnSize)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && IntArray::full(__return, numsSize, l1) && *returnSize == numsSize
*/
{
    *returnSize = numsSize;
    
    for (int i = 1; i < numsSize; ++i) {
        int key = nums[i];
        int j = i - 1;
        
        while (j >= 0 && nums[j] > key) {
            nums[j + 1] = nums[j];
            j--;
        }
        nums[j + 1] = key;
    }
    return nums;
}
