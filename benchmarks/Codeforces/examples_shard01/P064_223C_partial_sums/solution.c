/*
 * Codeforces 223/C - Partial Sums  (rating 1900, COMBINATORICS)
 *
 * Applying the prefix-sum operator k times sends a_j to position i with the
 * multiplicity C(k-1 + i-j, i-j) (a standard stars-and-bars count of the ways
 * to distribute the k rounds).  n <= 2000, so evaluate that convolution
 * directly after building the coefficients incrementally.
 */

#include <stdio.h>

#define MOD 1000000007LL

/* power: modular exponentiation, used for the modular inverse. */
static long long power(long long b, long long e)
{
    long long r = 1;
    b %= MOD;
    while (e) {
        if (e & 1)
            r = r * b % MOD;
        b = b * b % MOD;
        e >>= 1;
    }
    return r;
}

/* solver: pure.  out[i] = sum_j C(k-1+i-j, i-j) * a[j] (mod 1e9+7). */
static void solver(const long long *a, int n, long long k, long long *out,
                   long long *coef)
{
    if (k == 0) {
        for (int i = 0; i < n; i++)
            out[i] = a[i] % MOD;
        return;
    }
    coef[0] = 1;
    for (int d = 1; d < n; d++)           /* C(k-1+d, d) from C(k-1+d-1, d-1) */
        coef[d] = coef[d - 1] % MOD * ((k - 1 + d) % MOD) % MOD
                  * power(d, MOD - 2) % MOD;
    for (int i = 0; i < n; i++) {
        long long s = 0;
        for (int j = 0; j <= i; j++)
            s = (s + coef[i - j] * (a[j] % MOD)) % MOD;
        out[i] = s;
    }
}

int main(void)
{
    int n;
    long long k;
    if (scanf("%d %lld", &n, &k) != 2)
        return 0;
    static long long a[2005], out[2005], coef[2005];
    for (int i = 0; i < n; i++)
        scanf("%lld", &a[i]);
    solver(a, n, k, out, coef);
    for (int i = 0; i < n; i++)
        printf("%lld%c", out[i], i + 1 == n ? '\n' : ' ');
    return 0;
}
