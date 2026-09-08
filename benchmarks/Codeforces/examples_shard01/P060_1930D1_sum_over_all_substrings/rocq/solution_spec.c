/*
 * Codeforces 1930/D1 - Sum over all Substrings (Easy)  (rating 1800, OTHER)
 *
 * f(p) (minimum 1s in a p-good string) is computed greedily: scan left to
 * right; whenever an uncovered '1' is seen at position k, place a single 1 that
 * covers positions k, k+1, k+2 (advance the cover to k+2), counting one. This
 * greedy is prefix-consistent, so for a fixed left end i the running count
 * equals f(s[i..k]); summing over all k and all i gives the answer.
 */

// #include <stdio.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P060_1930D1_sum_over_all_substrings.rocq.spec_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
*/

/* solver: pure. Returns the sum of f over all substrings of s[0..n-1]. */
static long long solver(const char *s, int n)
/*@ With (bits : list Z)
    Require
      1 <= n && n <= 100 && (forall i, (0 <= i && i < n) => (bits[i] == 48 || bits[i] == 49)) &&
      n == Zlength(bits) && CharArray::full(s, n, bits)
    Ensure
      Spec(bits, __return) &&
      CharArray::full(s, n, bits)
*/
{
    long long total = 0;
    for (int i = 0; i < n; i++) {
        int cover = i - 1;        /* positions <= cover already accounted for */
        long long cnt = 0;
        for (int k = i; k < n; k++) {
            if (s[k] == '1' && k > cover) { cnt++; cover = k + 2; }
            total += cnt;         /* cnt == f(s[i..k]) */
        }
    }
    return total;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n;
//         char s[105];
//         scanf("%d %104s", &n, s);
//         printf("%lld\n", solver(s, n));
//     }
//     return 0;
// }
