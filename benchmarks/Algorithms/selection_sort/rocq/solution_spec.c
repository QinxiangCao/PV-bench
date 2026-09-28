/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
 */
/*@ Extern Coq
      (increasing : list Z -> Prop)
 */

/*@ Import Coq Require Import PVbench.Algorithms.selection_sort.rocq.spec_lib */

void sortArray(int* nums, int numsSize) 
/*@ With (l: list Z)
    Require 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && IntArray::full(nums, numsSize, l1)
*/
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
