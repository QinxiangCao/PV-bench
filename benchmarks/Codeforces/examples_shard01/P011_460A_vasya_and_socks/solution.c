/*
 * Codeforces 460/A - Vasya and Socks  (rating 900, IMPLEMENTATION)
 *
 * Simulate day by day: each day uses one pair, and every m-th evening adds
 * one; n, m <= 100 so the loop is tiny.
 */

#include <stdio.h>

/* solver: pure.  Number of consecutive days until the socks run out. */
static int solver(int n, int m)
{
    int days = 0;
    while (n > 0) {
        days++;
        n--;
        if (days % m == 0)
            n++;
    }
    return days;
}

int main(void)
{
    int n, m;
    if (scanf("%d %d", &n, &m) != 2)
        return 0;
    printf("%d\n", solver(n, m));
    return 0;
}
