/*
 * Codeforces 26/A - Almost Prime  (rating 900, NUMBER THEORY)
 *
 * A sieve counts, for every value up to n, how many distinct primes divide it;
 * the answer is how many of them have exactly two.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P008_26A_almost_prime.rocq.spec_lib */

#define MAXN 3005

/* solver: pure.  Count of almost primes (exactly 2 distinct prime divisors)
 * in [1, n]. */
static int solver(int n)
/*@
    Require
      1 <= n && n <= 3000 &&
      emp
    Ensure
      Spec(n, __return) &&
      emp
*/
{
    int ndiv[MAXN] = {0};
    for (int p = 2; p <= n; p++)
        if (ndiv[p] == 0)                 /* p is prime */
            for (int m = p; m <= n; m += p)
                ndiv[m]++;
    int cnt = 0;
    for (int v = 1; v <= n; v++)
        if (ndiv[v] == 2)
            cnt++;
    return cnt;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     printf("%d\n", solver(n));
//     return 0;
// }
