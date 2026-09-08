/*
 * Codeforces 1436/F - Sum Over Subsets  (rating 2800, NUMBER THEORY)
 *
 * Count first for every d the sets whose elements are all divisible by d, then
 * peel off the multiples to keep only gcd exactly d.  Over a pool of k items
 * with sum S and square-sum S2, summing sum(A)*sum(B) over all (A, B) with
 * B = A minus one element gives
 *     S2 * 2^(k-2) * (k-1)  +  (S^2 - S2) * (2^(k-3)*(k-2) + 2^(k-2)),
 * since a_i^2 appears once per element dropped from A, and a_i*a_j appears
 * both when a third element is dropped and when a_i itself is the dropped one.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MOD 998244353LL
#define MAXV 100001

static long long powmod(long long b, long long e)
{
    long long r = 1;
    b %= MOD;
    if (b < 0)
        b += MOD;
    while (e > 0) {
        if (e & 1)
            r = r * b % MOD;
        b = b * b % MOD;
        e >>= 1;
    }
    return r;
}

/* pool_sum: the contribution of a pool of k items with sums S and S2. */
static long long pool_sum(long long k, long long S, long long S2)
{
    if (k < 2)
        return 0;
    long long cross = ((S * S - S2) % MOD + MOD) % MOD;
    long long p2 = powmod(2, k - 2);
    long long total = S2 % MOD * p2 % MOD * ((k - 1) % MOD) % MOD;
    long long second = p2;                /* the 2^(k-2) term */
    if (k >= 3)
        second = (second + powmod(2, k - 3) * ((k - 2) % MOD)) % MOD;
    total = (total + cross * second) % MOD;
    return total;
}

/* solver: the required sum over all valid (A, B) with gcd(A) = 1. */

static long long solver(const long long *cnt, const long long *sum,
                        const long long *sqsum, long long *ans, int maxv)
{
    for (int d = maxv; d >= 1; d--) {
        long long k = 0, S = 0, S2 = 0;
        for (int v = d; v <= maxv; v += d) {
            k += cnt[v];
            S = (S + sum[v]) % MOD;
            S2 = (S2 + sqsum[v]) % MOD;
        }
        long long cur = pool_sum(k, S, S2);
        for (int v = 2 * d; v <= maxv; v += d)
            cur = (cur - ans[v] % MOD + MOD) % MOD;
        ans[d] = cur;
    }
    return ans[1];
}

int main(void)
{
    int m;
    if (scanf("%d", &m) != 1)
        return 0;
    static long long cnt[MAXV], sum[MAXV], sqsum[MAXV], ans[MAXV];
    int maxv = 1;
    for (int i = 0; i < m; i++) {
        long long a, f;
        scanf("%lld %lld", &a, &f);
        cnt[a] += f;
        sum[a] = (sum[a] + a % MOD * (f % MOD)) % MOD;
        sqsum[a] = (sqsum[a] + a % MOD * (a % MOD) % MOD * (f % MOD)) % MOD;
        if (a > maxv)
            maxv = (int)a;
    }
    printf("%lld\n", solver(cnt, sum, sqsum, ans, maxv));
    return 0;
}
