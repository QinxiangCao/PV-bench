/*
 * Codeforces 1102/C - Doors Breaking and Repairing  (rating 1200, GAMES)
 *
 * If x > y every door falls: you always out-damage the repair.  Otherwise only
 * doors with a_i <= x can ever be zeroed (one hit), and Slavik protects one
 * such door after each of your breaks, so you get every other one: the answer
 * is ceil(cnt / 2) where cnt counts doors with a_i <= x.
 */

#include <stdio.h>

/* solver: pure.  Number of doors ending at durability 0 under optimal play. */
static int solver(const int *a, int n, int x, int y)
{
    if (x > y)
        return n;
    int cnt = 0;
    for (int i = 0; i < n; i++)
        if (a[i] <= x)
            cnt++;
    return (cnt + 1) / 2;
}

int main(void)
{
    int n, x, y;
    if (scanf("%d %d %d", &n, &x, &y) != 3)
        return 0;
    static int a[105];
    for (int i = 0; i < n; i++)
        scanf("%d", &a[i]);
    printf("%d\n", solver(a, n, x, y));
    return 0;
}
