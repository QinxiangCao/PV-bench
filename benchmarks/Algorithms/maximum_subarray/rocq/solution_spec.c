/*@ Extern Coq
      (MaxSubarraySumPrefix : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.maximum_subarray.rocq.spec_lib */

int max(int a, int b)

{
    return (a > b) ? a : b;
}

int max_sub_array(int *arr, int n)
/*@ With (l : list Z)
    Require
      1 <= n && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l) &&
      (forall (k : Z), (0 <= k && k < n) => (-10000 <= l[k] && l[k] <= 10000))
    Ensure
      MaxSubarraySumPrefix(l, n, __return) &&
      IntArray::full(arr, n, l)
 */
{
    if (n == 0) {
        return 0;
    }

    int cur = arr[0]; 
    int res = arr[0];  

    for (int i = 1; i < n; i++) {

        cur = max(arr[i], cur + arr[i]);

        res = max(res, cur);

    }

    return res;
}
