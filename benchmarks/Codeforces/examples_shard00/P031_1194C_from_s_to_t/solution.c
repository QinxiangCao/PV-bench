/* Codeforces 1194/C - From S To T */
#include <stdio.h>
#include <string.h>

static int solver(const char *s, const char *t, const char *p)
{
    int i = 0, cnt[26] = {0};
    for (int j = 0; t[j]; ++j) if (s[i] && s[i] == t[j]) ++i;
    if (s[i]) return 0;
    for (i = 0; s[i]; ++i) ++cnt[s[i] - 'a'];
    for (i = 0; p[i]; ++i) ++cnt[p[i] - 'a'];
    for (i = 0; t[i]; ++i) if (--cnt[t[i] - 'a'] < 0) return 0;
    return 1;
}

int main(void)
{
    int q; scanf("%d", &q);
    while (q--) {
        char s[105], t[105], p[105]; scanf("%104s %104s %104s", s, t, p);
        puts(solver(s, t, p) ? "YES" : "NO");
    }
    return 0;
}
