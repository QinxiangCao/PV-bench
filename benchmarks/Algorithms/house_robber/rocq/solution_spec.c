/*@ Extern Coq
      (HouseRobberAnswer : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.house_robber.rocq.spec_lib */

int rob(int *nums, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(nums, n, l) &&
      (forall (k : Z), (0 <= k && k < n) => (0 <= l[k] && l[k] <= 10000))
    Ensure
      HouseRobberAnswer(l, __return) &&
      0 <= __return && __return <= 1000000000 &&
      IntArray::full(nums, n, l)
 */
{
  int prev2 = 0;
  int prev1 = 0;

  for (int i = 0; i < n; ++i) {
    int take = prev2 + nums[i];
    int skip = prev1;
    int cur;
    if (take > skip) {
      cur = take;
    } else {
      cur = skip;
    }

    prev2 = prev1;
    prev1 = cur;
  }
  return prev1;
}
