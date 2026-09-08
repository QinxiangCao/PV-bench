/* Codeforces 1054/C - Candies Distribution */
#include <stdio.h>

static int solver(int n, const int *l, const int *r, int *a)
{
    for (int i = 0; i < n; ++i) a[i] = n - l[i] - r[i];
    for (int i = 0; i < n; ++i) {
        int cl = 0, cr = 0;
        for (int j = 0; j < i; ++j) cl += a[j] > a[i];
        for (int j = i + 1; j < n; ++j) cr += a[j] > a[i];
        if (a[i] < 1 || cl != l[i] || cr != r[i]) return 0;
    }
    return 1;
}

int main(void)
{
    int n, l[1000], r[1000], a[1000];
    if (scanf("%d", &n) != 1) return 0;
    for (int i = 0; i < n; ++i) scanf("%d", &l[i]);
    for (int i = 0; i < n; ++i) scanf("%d", &r[i]);
    if (!solver(n, l, r, a)) { puts("NO"); return 0; }
    puts("YES");
    for (int i = 0; i < n; ++i) printf("%d%c", a[i], i + 1 == n ? '\n' : ' ');
    return 0;
}
