/*
 * Codeforces 649/C - Printing Statements  (rating 1500, GREEDY)
 *
 * Serving the cheapest sets first maximises the count.  For one set, spend
 * double-sided sheets first (they cover two pages each) and finish the tail
 * with single-sided ones; that consumes the least paper for that set.
 */

#include <stdio.h>
#include <stdlib.h>

static int cmp_int(const void *a, const void *b)
{
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

/* solver: maximum number of teams served.  Sorts a[] ascending. */
static int solver(int *a, int n, long long x, long long y)
{
    qsort(a, n, sizeof *a, cmp_int);
    int served = 0;
    for (int i = 0; i < n; i++) {
        long long pages = a[i];
        long long use = pages / 2;
        if (use > x)
            use = x;
        x -= use;
        pages -= 2 * use;
        if (pages > 0) {
            if (pages <= y)
                y -= pages;               /* finish on single-sided sheets */
            else if (pages == 1 && x > 0)
                x--;                      /* one page on a fresh double sheet */
            else
                break;
        }
        served++;
    }
    return served;
}

int main(void)
{
    int n;
    long long x, y;
    if (scanf("%d %lld %lld", &n, &x, &y) != 3)
        return 0;
    static int a[200005];
    for (int i = 0; i < n; i++)
        scanf("%d", &a[i]);
    printf("%d\n", solver(a, n, x, y));
    return 0;
}
