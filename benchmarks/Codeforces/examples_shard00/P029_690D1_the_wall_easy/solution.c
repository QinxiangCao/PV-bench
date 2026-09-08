/* Codeforces 690/D1 - The Wall (easy) */
#include <stdio.h>

static int solver(const char grid[][105], int r, int c)
{
    int occupied[100] = {0};
    for (int i = 0; i < r; ++i)
        for (int j = 0; j < c; ++j) if (grid[i][j] == 'B') occupied[j] = 1;
    int segments = 0;
    for (int j = 0; j < c; ++j)
        if (occupied[j] && (j == 0 || !occupied[j - 1])) ++segments;
    return segments;
}

int main(void)
{
    int r, c; char grid[100][105];
    if (scanf("%d %d", &r, &c) != 2) return 0;
    for (int i = 0; i < r; ++i) scanf("%104s", grid[i]);
    printf("%d\n", solver(grid, r, c));
    return 0;
}
