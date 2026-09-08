/*
 * Codeforces 1311/C - Perform the Combo  (rating 1300, BRUTE FORCE)
 *
 * Position j (0-based) is pressed once per try that reaches past it: that is
 * the number of p_i > j, plus the final successful try.  A difference array
 * over the p values turns that into one linear pass.
 */

#include <stdio.h>
#include <string.h>

static long long diff[200006];            /* work array, cleared on every call */

/* solver: reads no input.  cover[j] = number of tries pressing s[j]; accumulates
 * the per-letter totals into cnt[26]. */
static void solver(const char *s, int n, const int *p, int m, long long *cnt)
{
    memset(diff, 0, sizeof(long long) * (n + 1));   /* p_i may be n, so n + 1 */
    for (int i = 0; i < m; i++) {         /* try i presses s[0 .. p_i-1] */
        diff[0] = diff[0] + 1;
        diff[p[i]] = diff[p[i]] - 1;
    }
    diff[0] = diff[0] + 1;                /* the final, successful try */
    memset(cnt, 0, sizeof(long long) * 26);
    long long cover = 0;
    for (int j = 0; j < n; j++) {
        cover += diff[j];
        cnt[s[j] - 'a'] += cover;
    }
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static char s[200005];
    static int p[200005];
    long long cnt[26];
    while (t--) {
        int n, m;
        scanf("%d %d", &n, &m);
        scanf("%200004s", s);
        for (int i = 0; i < m; i++)
            scanf("%d", &p[i]);
        solver(s, n, p, m, cnt);
        for (int c = 0; c < 26; c++)
            printf("%lld%c", cnt[c], c == 25 ? '\n' : ' ');
    }
    return 0;
}
