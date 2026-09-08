/*
 * Codeforces 1382/B - Sequential Nim  (rating 1100, GAMES)
 *
 * Piles of exactly one stone force a move; piles with more than one let the
 * player on turn decide who faces the next pile (take all, or all but one).
 * So whoever first reaches a pile > 1 wins: with c leading ones, that is the
 * first player iff c is even.  If every pile is a single stone, parity of n
 * decides.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (SolverReturnBridge : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P018_1382B_sequential_nim.rocq.spec_lib */

/* solver: pure.  1 if the first player wins on piles a[0..n-1]. */
static int solver(const int *a, int n)
/*@ With (piles : list Z)
    Require
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (1 <= piles[i] && piles[i] <= 1000000000)) &&
      n == Zlength(piles) && IntArray::full(a, n, piles)
    Ensure
      exists (out : Z),
        Spec(piles, out) &&
        SolverReturnBridge(out, __return) && IntArray::full(a, n, piles)
*/
{
    int c = 0;
    while (c < n && a[c] == 1)
        c++;
    if (c == n)                     /* all piles are single stones */
        return n % 2 == 1;
    return c % 2 == 0;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[100005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         puts(solver(a, n) ? "First" : "Second");
//     }
//     return 0;
// }
