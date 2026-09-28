/* Codeforces 1207/B - Square Filling */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

typedef struct
{
    int r, c;
} Operation;

static int solver(int n, int m, const int a[50][50],
                  Operation *ops)

{
    int made[50 * 50] = {0}, count = 0;

    for (int i = 0; i + 1 < n; ++i)

        for (int j = 0; j + 1 < m; ++j)
        {
            if (a[i][j] && a[i + 1][j] && a[i][j + 1] && a[i + 1][j + 1])
            {

                ((int *)ops)[2 * count] = i + 1;
                ((int *)ops)[2 * count + 1] = j + 1;
                count++;

                made[i * 50 + j] = 1;
                made[(i + 1) * 50 + j] = 1;
                made[i * 50 + (j + 1)] = 1;
                made[(i + 1) * 50 + (j + 1)] = 1;
            }
        }

    for (int i = 0; i < n; ++i)

        for (int j = 0; j < m; ++j)
            if (a[i][j] != made[i * 50 + j])
                return -1;
    return count;
}

int main(void)
{
    int n, m, a[50][50]; Operation ops[2500];
    if (scanf("%d %d", &n, &m) != 2) return 0;
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < m; ++j) scanf("%d", &a[i][j]);
    int count = solver(n, m, a, ops);
    if (count < 0) { puts("-1"); return 0; }
    printf("%d\n", count);
    for (int i = 0; i < count; ++i) printf("%d %d\n", ops[i].r, ops[i].c);
    return 0;
}
