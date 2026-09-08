/*
 * Codeforces 1750/F - Majority  (rating 2700, COMBINATORICS DP)
 *
 * A string is rated iff, reading left to right, each maximal block of ones can
 * swallow the next one: blocks of sizes p and q separated by z zeros merge iff
 * p + q >= z.  So let A[i] count the rated strings of length i and B[i][j] the
 * strings of length i whose greedily merged prefix stops at length j; then
 *   A[i] = 2^(i-1) - sum_{j<i} A[j] * W[i-j][j],
 * where W[d][j] counts the blocked tails of length d after a block of j.
 * Splitting W by whether the following block's own merged prefix is capped by
 * its length or by the gap turns it into a power of two plus Q[d-j-1], where
 * Q[D] sums the prefix counts over all splits L + t = D with t < L.  Q depends
 * only on D, so everything runs in O(n^2) with O(n) memory per row and only
 * additions and multiplications, which suits the arbitrary modulus.
 */

#include <stdio.h>
#include <stdlib.h>

void *malloc(unsigned long size)
;

void free(void *ptr)
;

/* solver: number of rated strings of length n, modulo m. */
static long long solver(int n, long long m)
{
    long long *A = malloc((unsigned long)(n + 2) * sizeof(long long));
    long long *Q = malloc((unsigned long)(2 * n + 4) * sizeof(long long));
    long long *pow2 = malloc((unsigned long)(n + 2) * sizeof(long long));
    long long *Brow = malloc((unsigned long)(n + 2) * sizeof(long long));
    long long *P = malloc((unsigned long)(n + 2) * sizeof(long long));

    int i;
    for (i = 0; i < n + 2; i++) {       /* malloc does not zero: Q is read
                                             * before it is written, and A[j]
                                             * for j > i must read as 0 */
        A[i] = 0;
        Brow[i] = 0;
        P[i] = 0;
    }
    for (i = 0; i < 2 * n + 4; i++)
        Q[i] = 0;
    pow2[0] = 1 % m;
    for (i = 1; i <= n; i++)
        pow2[i] = pow2[i - 1] * 2 % m;

    for (i = 1; i <= n; i++) {
        long long blocked = 0;
        for (int j = 1; j < i; j++) {
            int d = i - j;
            /* W[d][j] = 1 (all-zero tail)
             *         + (2^Lmax - 1) for the gaps wide enough to cap the next
             *           block by its own length
             *         + Q[d-j-1] for the rest */
            long long w = 1 % m;
            int z0 = (d + j + 2) / 2;     /* ceil((d+j+1)/2) */
            int Lmax = d - z0;
            if (Lmax >= 1) {
                w = (w + pow2[Lmax] - 1 % m + m) % m;
            }
            int D = d - j - 1;
            if (D >= 0) {
                w = (w + Q[D]) % m;
            }
            Brow[j] = A[j] * w % m;
            blocked = (blocked + Brow[j]) % m;
        }
        A[i] = ((pow2[i - 1] - blocked) % m + m) % m;

        /* row of "maximal merged prefix = q" counts, then its prefix sums */
        long long run = 0;
        for (int q = 0; q <= i; q++) {
            long long c = (q == 0) ? 0 : (q < i ? Brow[q] : A[i]);
            run = (run + c) % m;
            P[q] = run;
        }
        for (int t = 0; t < i; t++)       /* feed Q[L+t] for t < L = i */
            if (i + t <= 2 * n)
                Q[i + t] = (Q[i + t] + P[t]) % m;
    }
    long long ans = A[n];
    free(A); free(Q); free(pow2); free(Brow); free(P);
    return ans;
}

int main(void)
{
    int n;
    long long m;
    if (scanf("%d %lld", &n, &m) != 2)
        return 0;
    printf("%lld\n", solver(n, m));
    return 0;
}
