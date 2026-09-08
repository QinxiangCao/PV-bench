/* Codeforces 38/A - Army */
#include <stdio.h>

static int solver(const int *d, int a, int b)
{
    int ans = 0;
    for (int i = a; i < b; ++i) ans += d[i];
    return ans;
}

int main(void)
{
    int n, d[101] = {0}, a, b;
    if (scanf("%d", &n) != 1) return 0;
    for (int i = 1; i < n; ++i) scanf("%d", &d[i]);
    scanf("%d %d", &a, &b);
    printf("%d\n", solver(d, a, b));
    return 0;
}
