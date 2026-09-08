/*
 * Codeforces 1266/C - Diverse Matrix  (rating 1400, CONSTRUCTIVE)
 *
 * The r+c gcds are distinct positive integers, so the magnitude is at least
 * r+c; a[i][j] = (c+i)*j attains it when r >= 2: row i has gcd (c+i) because
 * gcd(1..c) = 1, and column j has gcd j because consecutive integers c+1..c+r
 * are coprime as a set.  A single row (r = 1) instead uses a[1][j] = j+1, and
 * the 1x1 case is impossible since its two gcds coincide.
 */

#include <stdio.h>

/* solver: pure.  Fills m[i][j] (row-major, c columns) with a diverse matrix of
 * minimum magnitude; returns 0 if none exists. */

static int solver(int r, int c, int *m)
{
    if (r == 1 && c == 1)
        return 0;
    if (r == 1) {
        for (int j = 1; j <= c; j++)
            m[j - 1] = j + 1;             /* cols 2..c+1, row gcd 1 */
        return 1;
    }
    for (int i = 1; i <= r; i++)
        for (int j = 1; j <= c; j++)
            m[(i - 1) * c + (j - 1)] = (c + i) * j;
    return 1;
}

int main(void)
{
    int r, c;
    if (scanf("%d %d", &r, &c) != 2)
        return 0;
    static int m[500 * 500];
    if (!solver(r, c, m)) {
        puts("0");
        return 0;
    }
    for (int i = 0; i < r; i++)
        for (int j = 0; j < c; j++)
            printf("%d%c", m[i * c + j], j + 1 == c ? '\n' : ' ');
    return 0;
}
