/* Codeforces 1744/C - Traffic Light */
#include <stdio.h>
#include <string.h>

static int solver(const char *s, int n, char c)
{
    if (c == 'g') return 0;
    int ans = 0, next_green = -1;
    for (int i = 2 * n - 1; i >= 0; --i) {
        char ch = s[i % n];
        if (ch == 'g') next_green = i;
        if (i < n && ch == c && next_green - i > ans) ans = next_green - i;
    }
    return ans;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; char c, s[200005];
        scanf("%d %c %200004s", &n, &c, s);
        printf("%d\n", solver(s, n, c));
    }
    return 0;
}
