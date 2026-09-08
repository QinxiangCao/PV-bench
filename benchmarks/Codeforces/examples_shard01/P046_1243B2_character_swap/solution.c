/*
 * Codeforces 1243/B2 - Character Swap (Hard Version)  (rating 1600, STRINGS)
 *
 * Solvable iff every letter occurs an even number of times overall.  Fix
 * positions left to right: to repair position i, find another copy of s[i]
 * further right — in s[j], which takes one swap (s_j <-> t_i), or in t[j],
 * which first needs s_j <-> t_j to move it into s.  That is at most 2 swaps
 * per position, so at most 2n in total.
 */

#include <stdio.h>
#include <string.h>

/* solver: pure.  Fills oi/oj with the swap pairs (1-based) and returns the
 * number of swaps, or -1 if the strings cannot be made equal.  s and t are
 * modified into their final (equal) state. */
static int solver(char *s, char *t, int n, int *oi, int *oj)
{
    int cnt[26] = {0};
    for (int i = 0; i < n; i++) {
        cnt[s[i] - 'a']++;
        cnt[t[i] - 'a']++;
    }
    for (int c = 0; c < 26; c++)
        if (cnt[c] % 2) {
            return -1;
        }

    int m = 0;
    for (int i = 0; i < n; i++) {
        if (s[i] == t[i])
            continue;
        int j;
        for (j = i + 1; j < n; j++)
            if (s[j] == s[i])
                break;
        if (j < n) {                       /* one swap: s_j <-> t_i */
            char tmp = s[j];
            s[j] = t[i];
            t[i] = tmp;
            oi[m] = j + 1;
            oj[m] = i + 1;
            m++;
            continue;
        }
        for (j = i + 1; j < n; j++)
            if (t[j] == s[i])
                break;
        if (j >= n)
            return -1;                     /* cannot happen: counts are even */
        char tmp = s[j];                   /* move it into s: s_j <-> t_j */
        s[j] = t[j];
        t[j] = tmp;
        oi[m] = j + 1;
        oj[m] = j + 1;
        m++;
        tmp = s[j];                        /* then s_j <-> t_i */
        s[j] = t[i];
        t[i] = tmp;
        oi[m] = j + 1;
        oj[m] = i + 1;
        m++;
    }
    return m;
}

int main(void)
{
    int k;
    if (scanf("%d", &k) != 1)
        return 0;
    static char s[55], t[55];
    static int oi[205], oj[205];
    while (k--) {
        int n;
        scanf("%d %54s %54s", &n, s, t);
        int m = solver(s, t, n, oi, oj);
        if (m < 0) {
            puts("No");
            continue;
        }
        puts("Yes");
        printf("%d\n", m);
        for (int i = 0; i < m; i++)
            printf("%d %d\n", oi[i], oj[i]);
    }
    return 0;
}
