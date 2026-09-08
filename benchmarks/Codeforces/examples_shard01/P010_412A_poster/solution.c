/*
 * Codeforces 412/A - Poster  (rating 900, GREEDY)
 *
 * Every square must be painted, so the ladder has to visit all n positions;
 * the cheapest route walks to the nearer end first and then sweeps across.
 * Cost = (n-1) sweep steps + min(k-1, n-k) steps to reach that end + n prints.
 */

#include <stdio.h>

static void write_left(char dst[8])
{
    dst[0] = 'L';
    dst[1] = 'E';
    dst[2] = 'F';
    dst[3] = 'T';
    dst[4] = '\0';
}

static void write_right(char dst[8])
{
    dst[0] = 'R';
    dst[1] = 'I';
    dst[2] = 'G';
    dst[3] = 'H';
    dst[4] = 'T';
    dst[5] = '\0';
}

static void write_print(char dst[8], char ch)
{
    dst[0] = 'P';
    dst[1] = 'R';
    dst[2] = 'I';
    dst[3] = 'N';
    dst[4] = 'T';
    dst[5] = ' ';
    dst[6] = ch;
    dst[7] = '\0';
}

/* solver: pure.  Writes the optimal plan into out[] as one action per row
 * ("LEFT", "RIGHT" or "PRINT x") and returns the number of actions. */
static int solver(const char *s, int n, int k, char out[][8])
{
    int t = 0;
    if (k - 1 <= n - k) {                     /* walk left, then sweep right */
        for (int p = k; p > 1; p--)
            {
                write_left(out[t]);
                t++;
            }
        for (int p = 1; p <= n; p++) {
            write_print(out[t], s[p - 1]);
            t++;
            if (p < n)
                {
                    write_right(out[t]);
                    t++;
                }
        }
    } else {                                  /* walk right, then sweep left */
        for (int p = k; p < n; p++)
            {
                write_right(out[t]);
                t++;
            }
        for (int p = n; p >= 1; p--) {
            write_print(out[t], s[p - 1]);
            t++;
            if (p > 1)
                {
                    write_left(out[t]);
                    t++;
                }
        }
    }
    return t;
}

int main(void)
{
    int n, k;
    if (scanf("%d %d", &n, &k) != 2)
        return 0;
    static char s[105];
    scanf("%104s", s);
    static char out[305][8];
    int t = solver(s, n, k, out);
    for (int i = 0; i < t; i++)
        puts(out[i]);
    return 0;
}
