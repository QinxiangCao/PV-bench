/*@ Import Lean
import Codeforces.examples_shard01.P003_1438A_specific_tastes_of_andre.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 1438/A - Specific Tastes of Andre  (rating 800, CONSTRUCTIVE)
 *
 * If every element equals the same value v, a subarray of length L sums to
 * L*v, which is divisible by L.  So the constant array [1, 1, ..., 1] is
 * perfect and satisfies 1 <= a_i <= 100.
 */

// #include <stdio.h>
/*@ Extern Coq
        (Spec : Z -> list Z -> Prop)
*/
/* solver: pure.  Fills out[0..n-1] with a perfect array of length n. */
static void solver(int n, int *out)
/*@
    Require
      1 <= n && n <= 100 &&
      IntArray::undef_full(out, n)
    Ensure
      exists (out_spec : list Z),
        Spec(n, out_spec) &&
        IntArray::full(out, n, out_spec)
*/
{
    for (int i = 0; i < n; i++)
        out[i] = 1;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n;
//         static int out[105];
//         scanf("%d", &n);
//         solver(n, out);
//         for (int i = 0; i < n; i++)
//             printf("%d%c", out[i], i + 1 == n ? '\n' : ' ');
//     }
//     return 0;
// }
