/*
 * Codeforces 474/B - Worms  (rating 1200, BINARY SEARCH)
 *
 * Prefix sums give each pile's last label; a binary search over them maps a
 * queried label to its pile.
 */

#include <stdio.h>

/* solver: pure.  Index (1-based) of the pile holding label q, given the
 * prefix sums pre[1..n] of the pile sizes. */
static int locate_pile(const long long *pre, int n, long long q)
{
    int lo = 1, hi = n;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (pre[mid] >= q)
            hi = mid;
        else
            lo = mid + 1;
    }
    return lo;
}

/* solver: complete case.  Build prefix sums and answer the whole query list. */
static void solver(const int *piles, int n, const long long *queries, int m,
                   int *out, long long *pre)
{
    pre[0] = 0;
    for (int i = 0; i < n; i++) {
        pre[i + 1] = pre[i] + piles[i];
    }
    for (int i = 0; i < m; i++) {
        out[i] = locate_pile(pre, n, queries[i]);
    }
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static int piles[100005], out[100005];
    static long long pre[100005], queries[100005];
    for (int i = 0; i < n; i++)
        scanf("%d", &piles[i]);
    int m;
    scanf("%d", &m);
    for (int i = 0; i < m; i++)
        scanf("%lld", &queries[i]);
    solver(piles, n, queries, m, out, pre);
    for (int i = 0; i < m; i++)
        printf("%d\n", out[i]);
    return 0;
}
