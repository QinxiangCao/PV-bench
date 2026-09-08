/*@ Import Lean
import Codeforces.examples_shard01.P017_753A_santa_claus_and_candies.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 753/A - Santa Claus and Candies  (rating 1000, GREEDY)
 *
 * Handing out 1, 2, 3, ... keeps the totals as small as possible, so the
 * largest k is the one with k(k+1)/2 <= n.  Give 1..k and add the leftover
 * n - k(k+1)/2 (which is < k+1) to the last child, keeping all values distinct.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> list Z -> Prop)
*/
/* solver: pure.  Fills out[] with the gift sizes and returns their count. */
static int solver(int n, int *out)
/*@
    Require
      1 <= n && n <= 1000 &&
      IntArray::undef_full(out, n)
    Ensure
      exists (out_spec : list Z),
        Spec(n, out_spec) &&
        __return == Zlength(out_spec) && IntArray::full(out, Zlength(out_spec), out_spec) * IntArray::undef_seg(out, Zlength(out_spec), n)
*/
{
    int k = 0;
    long long used = 0;
    while (used + (k + 1) <= n) {
        k++;
        used += k;
    }
    for (int i = 0; i < k; i++)
        out[i] = i + 1;
    out[k - 1] += (int)(n - used);
    return k;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int out[100];
//     int k = solver(n, out);
//     printf("%d\n", k);
//     for (int i = 0; i < k; i++)
//         printf("%d%c", out[i], i + 1 == k ? '\n' : ' ');
//     return 0;
// }
