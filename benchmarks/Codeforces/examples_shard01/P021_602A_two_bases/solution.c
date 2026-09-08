/*
 * Codeforces 602/A - Two Bases  (rating 1100, IMPLEMENTATION)
 *
 * Both numbers have at most 10 digits in a base below 40, so their values fit
 * comfortably in a 64-bit integer (40^10 < 1.1e16); convert and compare.
 */

#include <stdio.h>

/* solver: pure.  Value of the digit string d[0..n-1] (most significant first)
 * read in base b. */
static long long numeral_value(const int *d, int n, int b)
{
    long long v = 0;
    for (int i = 0; i < n; i++)
        v = v * b + d[i];
    return v;
}

/* solver: complete case.  Return the ASCII comparison character required by
 * the statement, so its result has exactly the boundary of Spec. */
static int solver(int bx, int basey, const int *x, int n,
                  const int *y, int m)
{
    long long vx = numeral_value(x, n, bx);
    long long vy = numeral_value(y, m, basey);
    return vx < vy ? '<' : vx > vy ? '>' : '=';
}

int main(void)
{
    int n, bx, m, by;
    static int x[15], y[15];
    if (scanf("%d %d", &n, &bx) != 2)
        return 0;
    for (int i = 0; i < n; i++)
        scanf("%d", &x[i]);
    scanf("%d %d", &m, &by);
    for (int i = 0; i < m; i++)
        scanf("%d", &y[i]);
    putchar(solver(bx, by, x, n, y, m));
    putchar('\n');
    return 0;
}
