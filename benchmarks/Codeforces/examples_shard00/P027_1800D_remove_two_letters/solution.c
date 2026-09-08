/* Codeforces 1800/D - Remove Two Letters */
#include <stdio.h>

static int solver(const char *s, int n)
{
    int answer = n - 1;
    for (int i = 0; i + 2 < n; ++i) if (s[i] == s[i + 2]) --answer;
    return answer;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; char s[200005]; scanf("%d %200004s", &n, s);
        printf("%d\n", solver(s, n));
    }
    return 0;
}
