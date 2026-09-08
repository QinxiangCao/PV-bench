/*
 * Codeforces 817/A - Treasure Hunt  (rating 1200, VERDICT)
 *
 * Each potion use changes position by (+-x, +-y). Reachable iff |dx| is a
 * multiple of x, |dy| a multiple of y, and the two step counts dx/x and dy/y
 * have the same parity (every move flips both counts' parities together).
 */

#include <stdio.h>
#include <stdlib.h>

/* solver: pure. Returns 1 (YES) if the treasure is reachable, else 0. */
static int solver(long long x1, long long y1, long long x2, long long y2,
                  long long x, long long y)
{
    long long dx;
    long long dy;
    if (x1 >= x2) {
        dx = x1 - x2;
    } else {
        dx = x2 - x1;
    }
    if (y1 >= y2) {
        dy = y1 - y2;
    } else {
        dy = y2 - y1;
    }
    if (dx % x != 0 || dy % y != 0)
        return 0;
    return (dx / x) % 2 == (dy / y) % 2;
}

int main(void)
{
    long long x1, y1, x2, y2, x, y;
    if (scanf("%lld %lld %lld %lld %lld %lld", &x1, &y1, &x2, &y2, &x, &y) != 6)
        return 0;
    printf("%s\n", solver(x1, y1, x2, y2, x, y) ? "YES" : "NO");
    return 0;
}
