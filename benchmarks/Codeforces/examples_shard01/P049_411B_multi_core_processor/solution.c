/*
 * Codeforces 411/B - Multi-core Processor  (rating 1600, IMPLEMENTATION)
 *
 * Simulate cycle by cycle: within a cycle, count the live cores addressing
 * each cell.  A cell with two or more writers locks (with its writers), and a
 * write to an already locked cell locks that single core.
 */

#include <stdio.h>
#include <string.h>

#define MAXN 105

/* solver: pure.  x[i][j] instructions -> lock[i] = locking cycle or 0. */

static void solver(int n, int m, int k, const int x[][MAXN], int *lock)
{
    int cell_locked[MAXN] = {0};
    int writers[MAXN], first[MAXN];
    for (int i = 0; i < n; i++)
        lock[i] = 0;
    for (int j = 0; j < m; j++) {
        memset(writers, 0, sizeof(int) * (k + 1));
        for (int c = 1; c <= k; c++)
            first[c] = -1;
        for (int i = 0; i < n; i++) {
            if (lock[i] || x[i][j] == 0)
                continue;
            int c = x[i][j];
            if (cell_locked[c]) {
                lock[i] = j + 1;           /* writing to a dead cell */
                continue;
            }
            writers[c] = writers[c] + 1;
            if (first[c] < 0)
                first[c] = i;
        }
        for (int c = 1; c <= k; c++)
            if (writers[c] >= 2) {
                cell_locked[c] = 1;
                for (int i = 0; i < n; i++)
                    if (!lock[i] && x[i][j] == c)
                        lock[i] = j + 1;
            }
    }
}

int main(void)
{
    int n, m, k;
    if (scanf("%d %d %d", &n, &m, &k) != 3)
        return 0;
    static int x[MAXN][MAXN], lock[MAXN];
    for (int i = 0; i < n; i++)
        for (int j = 0; j < m; j++)
            scanf("%d", &x[i][j]);
    solver(n, m, k, x, lock);
    for (int i = 0; i < n; i++)
        printf("%d\n", lock[i]);
    return 0;
}
