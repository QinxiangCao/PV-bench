/*@ Extern Coq
      (IsMajorityElement : Z -> list Z -> Prop)
 */

/*@ Import Coq Require Import PVbench.Algorithms.majority_element.rocq.spec_lib */

int majorityElement(int* nums, int numsSize)
/*@ With (l : list Z)
    Require exists x, IsMajorityElement(x,l) && 1 <= numsSize && numsSize <= 50000 && Zlength(l) == numsSize && IntArray::full(nums, numsSize, l)
    Ensure IsMajorityElement(__return, l) && IntArray::full(nums, numsSize, l)
*/
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
