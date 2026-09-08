/*
 * Codeforces 1999/E - Triple Operations  (rating 1300, MATH)
 *
 * Write f(x) for the number of base-3 digits of x, i.e. how many divisions by
 * 3 drive x to 0.  Every operation performs one division on some y (and one
 * multiplication, which is free if x is already 0).  Zeroing the smallest
 * number l first costs f(l), and pairing it with each remaining number costs
 * f(i) each, so the total is 2*f(l) + sum_{i=l+1..r} f(i).
 *
 * The tables are shared by every query, so solver() takes the whole query set
 * and builds them itself; main() only reads and prints.
 */

#include <stdio.h>

#define MAXN 200005
#define MAXQ 10005

static long long pre[MAXN];               /* pre[i] = sum of f(1..i) */
static int fv[MAXN];                      /* fv[i]  = f(i) */

/* solver: reads no input.  Answers query i as out[i], for l[i] < r[i].  Builds
 * the file-scope tables `fv` and `pre` on every call, so it is not free of
 * global-state writes. */
static void solver(int q, const int *l, const int *r, long long *out)
{
    fv[0] = 0;
    pre[0] = 0;
    for (int i = 1; i < MAXN; i++) {
        fv[i] = fv[i / 3] + 1;
        pre[i] = pre[i - 1] + fv[i];
    }
    for (int i = 0; i < q; i++)
        out[i] = 2LL * fv[l[i]] + (pre[r[i]] - pre[l[i]]);
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static int l[MAXQ], r[MAXQ];
    static long long out[MAXQ];
    for (int i = 0; i < t; i++)
        scanf("%d %d", &l[i], &r[i]);
    solver(t, l, r, out);
    for (int i = 0; i < t; i++)
        printf("%lld\n", out[i]);
    return 0;
}
