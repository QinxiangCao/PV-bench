/*
 * Codeforces 1474/D - Cleaning  (rating 2200, PREFIX SUMS)
 *
 * Sweeping left to right, the stones pile i must hand to the right are forced:
 * pre[i] = a_i - pre[i-1], and the array clears iff every pre[i] >= 0 and
 * pre[n] == 0.  Build the mirrored suffix values too; a swap at (i, i+1) then
 * only needs the two middle values recomputed against pre[i-1] and suf[i+2].
 */

#include <stdio.h>

/* solver: 1 if all stones can be removed using at most one adjacent swap. */

static int solver(const long long *a, int n, long long *pre, long long *suf,
                  char *okpre, char *oksuf)
{
    pre[0] = 0;
    okpre[0] = 1;
    for (int i = 1; i <= n; i++) {
        pre[i] = a[i] - pre[i - 1];
        okpre[i] = okpre[i - 1] && pre[i] >= 0;
    }
    suf[n + 1] = 0;
    oksuf[n + 1] = 1;
    for (int i = n; i >= 1; i--) {
        suf[i] = a[i] - suf[i + 1];
        oksuf[i] = oksuf[i + 1] && suf[i] >= 0;
    }
    if (okpre[n] && pre[n] == 0)
        return 1;
    for (int i = 1; i < n; i++) {         /* swap piles i and i+1 */
        if (!okpre[i - 1] || !oksuf[i + 2])
            continue;
        long long x = a[i + 1] - pre[i - 1];
        if (x < 0)
            continue;
        long long y = a[i] - x;
        if (y < 0)
            continue;
        if (y == suf[i + 2])
            return 1;
    }
    return 0;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static long long a[200005], pre[200005], suf[200007];
    static char okpre[200005], oksuf[200007];
    while (t--) {
        int n;
        scanf("%d", &n);
        for (int i = 1; i <= n; i++)
            scanf("%lld", &a[i]);
        puts(solver(a, n, pre, suf, okpre, oksuf) ? "YES" : "NO");
    }
    return 0;
}
