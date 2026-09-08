/*
 * Codeforces 535/C - Tavas and Karafs  (rating 1900, BINARY SEARCH)
 *
 * The prefix l..r can be eaten in t m-bite moves iff the tallest karafs fits
 * (s_r <= t) and the total height fits (sum <= t*m).  Both conditions get
 * harder as r grows, so binary search the largest feasible r.
 */

#include <stdio.h>

/* height: s_i = A + (i-1)*B. */
static long long height(long long A, long long B, long long i)
{
    return A + (i - 1) * B;
}

/* range_sum: sum of s_l .. s_r (arithmetic progression). */
static long long range_sum(long long A, long long B, long long l, long long r)
{
    long long cnt = r - l + 1;
    return (height(A, B, l) + height(A, B, r)) * cnt / 2;
}

/* solver: pure.  Largest r with l <= r that can be eaten, or -1. */
static long long answer_query(long long A, long long B, long long l,
                              long long t, long long m)
{
    if (height(A, B, l) > t)
        return -1;
    long long lo = l, hi = l;
    while (height(A, B, hi) <= t)         /* find an upper bound first */
        hi *= 2;
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;
        if (height(A, B, mid) <= t && range_sum(A, B, l, mid) <= t * m)
            lo = mid;
        else
            hi = mid - 1;
    }
    return lo;
}

/* solver: complete case.  Answer the entire logical query list. */
static void solver(long long A, long long B, const long long *ql,
                   const long long *qt, const long long *qm, int n,
                   long long *out)
{
    for (int i = 0; i < n; i++)
        out[i] = answer_query(A, B, ql[i], qt[i], qm[i]);
}

int main(void)
{
    long long A, B;
    int n;
    if (scanf("%lld %lld %d", &A, &B, &n) != 3)
        return 0;
    static long long ql[100005], qt[100005], qm[100005], out[100005];
    for (int i = 0; i < n; i++)
        scanf("%lld %lld %lld", &ql[i], &qt[i], &qm[i]);
    solver(A, B, ql, qt, qm, n, out);
    for (int i = 0; i < n; i++)
        printf("%lld\n", out[i]);
    return 0;
}
