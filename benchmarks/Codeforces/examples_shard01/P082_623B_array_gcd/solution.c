/*
 * Codeforces 623/B - Array GCD  (rating 2300, DP)
 *
 * The removed segment cannot be the whole array, so a_1 or a_n survives, and
 * a surviving element is only changed by at most 1: every useful gcd divides
 * one of a_1-1, a_1, a_1+1, a_n-1, a_n, a_n+1.  For each prime factor p of
 * those six numbers, a three-state sweep (before the cut, inside it, after it)
 * gives the cheapest plan.
 */

#include <stdio.h>

#define INF (1LL << 62)

static void add_factors(long long v, long long *primes, int *nprime)
{
    for (long long d = 2; d * d <= v; d++)
        if (v % d == 0) {
            { primes[(*nprime)] = d; (*nprime)++; }
            while (v % d == 0)
                v /= d;
        }
    if (v > 1)
        { primes[(*nprime)] = v; (*nprime)++; }
}

/* solver: cheapest plan for the fixed prime p, or INF if impossible. */
static long long cost_for_prime(const int *arr, int n, long long a,
                                long long b, long long p)
{
    long long keep = 0, cutFresh = 0, cutAfterKeep = INF, after = INF;
    /* keep         : no cut yet, everything so far kept
     * cutFresh     : inside a cut that started at index 0
     * cutAfterKeep : inside a cut with at least one kept element before it
     * after        : the cut is finished, later elements are kept  */
    for (int i = 0; i < n; i++) {
        long long v = arr[i];
        long long cost;
        if (v % p == 0)
            cost = 0;
        else if ((v - 1) % p == 0 || (v + 1) % p == 0)
            cost = b;
        else
            cost = INF;

        long long nkeep = keep == INF || cost == INF ? INF : keep + cost;
        long long ncutFresh = cutFresh == INF ? INF : cutFresh + a;
        long long from = keep;             /* start a cut after kept elements */
        long long ncutAfterKeep = INF;
        if (i > 0 && from != INF)
            ncutAfterKeep = from + a;
        if (cutAfterKeep != INF && cutAfterKeep + a < ncutAfterKeep)
            ncutAfterKeep = cutAfterKeep + a;
        long long best_prev_cut = cutFresh < cutAfterKeep ? cutFresh : cutAfterKeep;
        long long nafter = INF;
        if (cost != INF) {
            if (best_prev_cut != INF)
                nafter = best_prev_cut + cost;
            if (after != INF && after + cost < nafter)
                nafter = after + cost;
        }
        keep = nkeep;
        cutFresh = ncutFresh;
        cutAfterKeep = ncutAfterKeep;
        after = nafter;
    }
    long long best = keep;
    if (after < best) best = after;
    if (cutAfterKeep < best) best = cutAfterKeep;   /* cut runs to the end */
    return best;
}

/* solver: complete case.  Enumerate every candidate prime internally. */
static long long solver(const int *arr, int n, long long a, long long b,
                        long long *primes)
{
    int nprime = 0;
    for (int d = -1; d <= 1; d++) {
        add_factors(arr[0] + d, primes, &nprime);
        add_factors(arr[n - 1] + d, primes, &nprime);
    }
    long long best = INF;
    for (int i = 0; i < nprime; i++) {
        long long r = cost_for_prime(arr, n, a, b, primes[i]);
        if (r < best)
            best = r;
    }
    return best;
}

int main(void)
{
    int n;
    long long a, b;
    if (scanf("%d %lld %lld", &n, &a, &b) != 3)
        return 0;
    static int arr[1000006];
    for (int i = 0; i < n; i++)
        scanf("%d", &arr[i]);
    static long long primes[256];
    printf("%lld\n", solver(arr, n, a, b, primes));
    return 0;
}
