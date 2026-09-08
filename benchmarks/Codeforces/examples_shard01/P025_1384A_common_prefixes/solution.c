/*
 * Codeforces 1384/A - Common Prefixes  (rating 1200, CONSTRUCTIVE)
 *
 * Keep one working string of 200 letters.  To realise a_i, copy the current
 * string and flip the letter at index a_i between 'a' and 'b': the first a_i
 * letters still agree and position a_i now differs, so the longest common
 * prefix is exactly a_i (a_i <= 50 < 200, so the index always exists).
 */

#include <stdio.h>

#define LEN 200

/* solver: pure.  Writes n+1 strings of length LEN into out[][], consecutive
 * ones having longest common prefix a[i]. */
static void solver(const int *a, int n, char out[][LEN + 1])
{
    for (int j = 0; j < LEN; j++)
        out[0][j] = 'a';
    out[0][LEN] = '\0';
    for (int i = 0; i < n; i++) {
        for (int j = 0; j <= LEN; j++)
            out[i + 1][j] = out[i][j];
        int k = a[i];
        out[i + 1][k] = out[i][k] == 'a' ? 'b' : 'a';
    }
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static int a[105];
    static char out[106][LEN + 1];
    while (t--) {
        int n;
        scanf("%d", &n);
        for (int i = 0; i < n; i++)
            scanf("%d", &a[i]);
        solver(a, n, out);
        for (int i = 0; i <= n; i++)
            puts(out[i]);
    }
    return 0;
}
