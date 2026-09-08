/*
 * Codeforces 1607/E - Robot on the Board 1  (rating 1600, IMPLEMENTATION)
 *
 * Track the robot's offset from its start and the running min/max of that
 * offset.  A prefix is survivable iff its row span is < n and column span < m;
 * take the longest such prefix and place the start so the visited window sits
 * flush inside the board.
 */

#include <stdio.h>

/* solver: pure.  Best starting cell (1-based) for command string s. */
static void solver(const char *s, int n, int m, int *row, int *col)
{
    int r = 0, c = 0;
    int minr = 0, maxr = 0, minc = 0, maxc = 0;
    int br = 0, bc = 0;                    /* answer for the longest prefix */
    *row = 1 - br;
    *col = 1 - bc;
    for (int i = 0; s[i]; i++) {
        switch (s[i]) {
        case 'U': r--; break;
        case 'D': r++; break;
        case 'L': c--; break;
        default:  c++; break;
        }
        int nminr = r < minr ? r : minr, nmaxr = r > maxr ? r : maxr;
        int nminc = c < minc ? c : minc, nmaxc = c > maxc ? c : maxc;
        if (nmaxr - nminr >= n || nmaxc - nminc >= m)
            break;                         /* this command would break it */
        minr = nminr; maxr = nmaxr;
        minc = nminc; maxc = nmaxc;
    }
    br = minr;
    bc = minc;
    *row = 1 - br;                         /* shift the window to the top-left */
    *col = 1 - bc;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static char s[1000006];
    while (t--) {
        int n, m, row, col;
        scanf("%d %d %1000005s", &n, &m, s);
        solver(s, n, m, &row, &col);
        printf("%d %d\n", row, col);
    }
    return 0;
}
