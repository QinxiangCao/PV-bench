/*
 * Codeforces 959/C - Mahmoud and Ehab and the wrong algorithm
 * (rating 1500, CONSTRUCTIVE)
 *
 * Section 2 (algorithm correct): the star centred at 1 has evenCnt = 1, which
 * is also the true cover size.
 *
 * Section 1 (algorithm wrong): a double star.  Centres 1 and 2 are adjacent,
 * each carrying at least two leaves; the true cover is {1, 2} of size 2 while
 * both depth classes hold at least three nodes, so the algorithm answers >= 3.
 * That needs n >= 6; for smaller n no counterexample exists.
 */

#include <stdio.h>

/* solver: pure.  Writes the counterexample tree's n-1 edges into eu/ev and
 * returns 1, or returns 0 when no counterexample exists. */
static int solver(int n, int *eu, int *ev)
{
    if (n < 6)
        return 0;
    int m = 0;
    { eu[m] = 1; ev[m] = 2; m++; } /* the two centres */
    { eu[m] = 1; ev[m] = 3; m++; } /* two leaves on centre 1 */
    { eu[m] = 1; ev[m] = 4; m++; }
    { eu[m] = 2; ev[m] = 5; m++; } /* two leaves on centre 2 */
    { eu[m] = 2; ev[m] = 6; m++; }
    for (int v = 7; v <= n; v++) {        /* the rest keeps both sides big */
        eu[m] = 1;
        { ev[m] = v; m++; }
    }
    return 1;
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static int eu[100005], ev[100005];
    if (solver(n, eu, ev))
        for (int i = 0; i < n - 1; i++)
            printf("%d %d\n", eu[i], ev[i]);
    else
        puts("-1");
    for (int v = 2; v <= n; v++)          /* section 2: star centred at 1 */
        printf("1 %d\n", v);
    return 0;
}
