/*@ Extern Coq
      (ClimbingStairsCount : Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.climbing_stairs.rocq.spec_lib */

int climbStairs(int n)
/*@ Require
      1 <= n && n <= 45 && emp
    Ensure
      ClimbingStairsCount(n, __return) && emp
 */
{
    int prev = 1;
    int curr = 1;
    int i = 2;

    while (i <= n) {
        int next = prev + curr;
        prev = curr;
        curr = next;
        i = i + 1;
    }

    return curr;
}
