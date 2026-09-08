/*
 * Codeforces 21/C - Stripe 2  (rating 2000, PREFIX SUMS)
 *
 * The total must split into three equal thirds.  Sweep the second cut from
 * left to right, counting on the way how many earlier positions carry prefix
 * sum S/3; whenever the prefix at the current position is 2S/3 those counted
 * positions each give one valid pair of cuts.
 */

#include <stdio.h>

/* solver: pure.  Number of ways to cut a[0..n-1] into three equal-sum parts. */
static long long solver(const long long *a, int n)
{
    long long total = 0;
    for (int i = 0; i < n; i++)
        total += a[i];
    if (total % 3 != 0)
        return 0;
    long long third = total / 3, run = 0, first = 0, ways = 0;
    for (int i = 0; i + 1 < n; i++) {     /* second cut goes after index i */
        run += a[i];
        if (i >= 1 && run == 2 * third)
            ways += first;
        if (run == third)
            first++;                      /* usable as a first cut later */
    }
    return ways;
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static long long a[100005];
    for (int i = 0; i < n; i++)
        scanf("%lld", &a[i]);
    printf("%lld\n", solver(a, n));
    return 0;
}
