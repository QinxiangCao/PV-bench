#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

typedef long long i64;
typedef struct
{
    int l, r;
} Seg;
static int cmp(const void *A, const void *B)
{
    const Seg *a = A, *b = B;
    return a->l == b->l ? a->r - b->r : a->l - b->l;
}
static int overlap(Seg *a, int na, Seg *b, int nb)

{
    if (!na || !nb)
        return 0;
    qsort(b, nb, sizeof *b, cmp)
        ;
    int *pref = malloc(nb * sizeof *pref)
        ;

    for (int i = 0; i < nb; i++)

        pref[i] = i && pref[i - 1] > b[i].r ? pref[i - 1] : b[i].r;
    int best = 0;

    for (int i = 0; i < na; i++)
    {
        int lo = 0, hi = nb;

        while (lo < hi)
        {
            int md = (lo + hi) / 2;

            if (b[md].l <= a[i].l)
                lo = md + 1;
            else
                hi = md;
        }

        if (lo)
        {
            int x = pref[lo - 1] < a[i].r ? pref[lo - 1] : a[i].r;
            x -= a[i].l;
            if (x > best)
                best = x;
        }
    }
    free(pref) ;
    return best;
}

static i64 solver(int n, const int *a,
                  const int *b)

{
    Seg *x = malloc(n * sizeof *x) ,
        *y = malloc(n * sizeof *y) ;
    int nx = 0, ny = 0;
    i64 base = 0;

    for (int i = 0; i < n; i++)
    {
        int d = a[i] - b[i];
        if (d < 0)
        {

            base -= d;
            x[nx].l = a[i];
            x[nx].r = b[i];
            nx++;
        }
        else if (d > 0)
        {

            base += d;
            y[ny].l = b[i];
            y[ny].r = a[i];
            ny++;
        }
    }

    int p = overlap(x, nx, y, ny)
        ,
        q = overlap(y, ny, x, nx),
        best = p > q ? p : q;

    free(y) ;
    free(x) ;
    return base - 2LL * best;
}
int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    int *a = malloc(n * sizeof *a), *b = malloc(n * sizeof *b);
    for (int i = 0; i < n; i++)
        scanf("%d", &a[i]);
    for (int i = 0; i < n; i++)
        scanf("%d", &b[i]);
    printf("%lld\n", solver(n, a, b));
    free(b);
    free(a);
    return 0;
}
