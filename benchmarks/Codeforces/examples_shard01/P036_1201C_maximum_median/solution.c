/*
 * Codeforces 1201/C - Maximum Median  (rating 1400, BINARY SEARCH)
 *
 * Reaching median m costs sum over the sorted upper half of max(0, m - a_i),
 * which grows with m, so binary search the largest affordable m.  Only the
 * upper half matters: raising smaller elements never helps the median.
 */

#include <stdio.h>
#include <stdlib.h>

static int cmp_int(const void *a, const void *b)
{
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

/* cost: operations needed to push the median of the sorted a[] up to m. */
static long long cost(const int *a, int n, long long m)
{
    long long need = 0;
    for (int i = n / 2; i < n; i++) {
        if (a[i] >= m)
            break;                        /* sorted: the rest are >= m too */
        need += m - a[i];
    }
    return need;
}

/* solver: largest achievable median within k operations.  Sorts a[]. */
static long long solver(int *a, int n, long long k)
{
    qsort(a, n, sizeof *a, cmp_int);
    long long lo = a[n / 2], hi = 2000000000LL;
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;
        if (cost(a, n, mid) <= k)
            lo = mid;
        else
            hi = mid - 1;
    }
    return lo;
}

int main(void)
{
    int n;
    long long k;
    if (scanf("%d %lld", &n, &k) != 2)
        return 0;
    static int a[200005];
    for (int i = 0; i < n; i++)
        scanf("%d", &a[i]);
    printf("%lld\n", solver(a, n, k));
    return 0;
}
