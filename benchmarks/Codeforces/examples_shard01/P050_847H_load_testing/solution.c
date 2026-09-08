/*
 * Codeforces 847/H - Load Testing  (rating 1600, GREEDY)
 *
 * Requests can only be added, so from the left the cheapest strictly
 * increasing profile is inc[i] = max(a[i], inc[i-1]+1), and symmetrically from
 * the right.  Trying every peak, the cost is the two prefix costs minus the
 * double-counted peak, whose value must be max(inc[i], dec[i]).
 */

#include <stdio.h>

/* solver: minimum requests to add.  pre/suf are scratch arrays of size n. */
static long long solver(const long long *a, int n, long long *inc,
                        long long *dec, long long *pre, long long *suf)
{
    inc[0] = a[0];
    for (int i = 1; i < n; i++)
        inc[i] = a[i] > inc[i - 1] + 1 ? a[i] : inc[i - 1] + 1;
    dec[n - 1] = a[n - 1];
    for (int i = n - 2; i >= 0; i--)
        dec[i] = a[i] > dec[i + 1] + 1 ? a[i] : dec[i + 1] + 1;

    pre[0] = inc[0] - a[0];
    for (int i = 1; i < n; i++)
        pre[i] = pre[i - 1] + (inc[i] - a[i]);
    suf[n - 1] = dec[n - 1] - a[n - 1];
    for (int i = n - 2; i >= 0; i--)
        suf[i] = suf[i + 1] + (dec[i] - a[i]);

    long long best = -1;
    for (int i = 0; i < n; i++) {
        long long peak = inc[i] > dec[i] ? inc[i] : dec[i];
        long long cost = pre[i] + suf[i] - (inc[i] - a[i]) - (dec[i] - a[i])
                         + (peak - a[i]);
        if (best < 0 || cost < best)
            best = cost;
    }
    return best;
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static long long a[100005], inc[100005], dec[100005], pre[100005], suf[100005];
    for (int i = 0; i < n; i++)
        scanf("%lld", &a[i]);
    printf("%lld\n", solver(a, n, inc, dec, pre, suf));
    return 0;
}
