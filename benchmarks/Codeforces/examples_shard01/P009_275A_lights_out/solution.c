/*
 * Codeforces 275/A - Lights Out  (rating 900, IMPLEMENTATION)
 *
 * Only the parity of each press count matters.  A light ends up on iff it was
 * toggled an even number of times, i.e. the sum of presses on itself and its
 * four side-adjacent cells is even (all lights start on).
 */

#include <stdio.h>

/* solver: pure.  press[3][3] press counts -> out[3][3] final states 0/1. */
static void solver(const int press[3][3], int out[3][3])
{
    const int di[5] = {0, -1, 1, 0, 0};
    const int dj[5] = {0, 0, 0, -1, 1};
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            int tog = 0;
            for (int d = 0; d < 5; d++) {
                int ni = i + di[d], nj = j + dj[d];
                if (ni >= 0 && ni < 3 && nj >= 0 && nj < 3)
                    tog += press[ni][nj];
            }
            out[i][j] = (tog % 2 == 0);       /* started on */
        }
}

int main(void)
{
    int press[3][3], out[3][3];
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            if (scanf("%d", &press[i][j]) != 1)
                return 0;
    solver(press, out);
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++)
            putchar('0' + out[i][j]);
        putchar('\n');
    }
    return 0;
}
