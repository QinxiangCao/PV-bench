/* Codeforces 2030/C - A TRUE Battle */
#include <stdio.h>

static int solver(const char *s, int n)
{
    if (s[0] == '1' || s[n - 1] == '1') return 1;
    for (int i = 0; i + 1 < n; ++i)
        if (s[i] == '1' && s[i + 1] == '1') return 1;
    return 0;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; char s[200005]; scanf("%d %200004s", &n, s);
        puts(solver(s, n) ? "YES" : "NO");
    }
    return 0;
}
