/*
 * Codeforces 1994/B - Fun Game  (rating 1100, VERDICT)
 *
 * The operation can flip bits of s only at positions >= the first '1' of s.
 * So: if s is all zeros, t must equal s. Otherwise, let i be the first '1' in
 * s; t must have only zeros before i (those bits are unreachable). Everything
 * from i onward can be set arbitrarily, so the answer is "Yes" in that case.
 */

#include <stdio.h>
#include <string.h>

/* solver: pure. Returns 1 ("Yes") if t is reachable from s, else 0. */
static int solver(const char *s, const char *t, int n)
{
    int i = 0;
    while (i < n && s[i] == '0')
        i++;

    if (i == n)                       /* s is all zeros */
        return strncmp(s, t, n) == 0;

    for (int j = 0; j < i; j++)       /* t must be zero before first 1 of s */
        if (t[j] != '0')
            return 0;
    return 1;
}

int main(void)
{
    int q;
    if (scanf("%d", &q) != 1)
        return 0;
    while (q--) {
        int n;
        scanf("%d", &n);
        static char s[200005], t[200005];
        scanf("%s %s", s, t);
        printf("%s\n", solver(s, t, n) ? "YES" : "NO");
    }
    return 0;
}
