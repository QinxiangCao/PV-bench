/*@ Import Lean
import Codeforces.examples_shard00.P003_1763A_absolute_maximization.lean.spec_lib
open scoped SimpleC
*/

/* Codeforces 1763/A - Absolute Maximization */
// #include <stdio.h>

/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/
static int solver(const int *a, int n)

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      3 <= Zlength(input) && Zlength(input) <= 512 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (0 <= input[i] && input[i] < 1024)) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 512)
    Ensure
      Spec(input, __return) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 512)
*/

{
    int all_or = 0, all_and = a[0];

    for (int i = 0; i < n; ++i) {
        all_or |= a[i];
        all_and &= a[i];
    }
    return all_or - all_and;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1) return 0;
//     while (t--) {
//         int n, a[512]; scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n));
//     }
//     return 0;
// }
