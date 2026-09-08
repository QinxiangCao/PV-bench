/*@ Import Lean
import Algorithms.split_array_largest_sum.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq
      (MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop)
 */
int check(int *arr, int n, int m, int cap)

{
  int cnt = 1;
  int cur = 0;

  for (int i = 0; i < n; ++i) {
    int x = arr[i];
    if (x > cap) {
      return 0;
    }
    if (cur + x > cap) {
      cnt = cnt + 1;
      cur = x;
    } else {
      cur = cur + x;
    }
  }
  if (cnt <= m) {
    return 1;
  } else {
    return 0;
  }
}

int splitArrayLargestSum(int *arr, int n, int m)
/*@ With (l : list Z)
    Require
      exists ans,
      1 <= n && n <= 100000 &&
      1 <= m && m <= n &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l) &&
      (forall (i : Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100000000)) &&

      MinimizedMaxSegmentSum(l, m, ans) &&
      0 <= ans &&
      ans <= 1000000000

    Ensure
      MinimizedMaxSegmentSum(l, m, __return) &&
      IntArray::full(arr, n, l)
 */
{
  int left = 0;
  int right = 1000000000;

  while (left < right) {
    int mid = left + (right - left) / 2;
    int ok = check(arr, n, m, mid);
    if (ok) {
      right = mid;
    } else {
      left = mid + 1;
    }
  }

  return left;
}
