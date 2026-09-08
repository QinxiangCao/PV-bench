/* Codeforces 1763/A - Absolute Maximization */
#include <stdio.h>

static int solver(const int *a, int n)
{
    int all_or = 0, all_and = a[0];
    for (int i = 0; i < n; ++i) {
        all_or |= a[i];
        all_and &= a[i];
    }
    return all_or - all_and;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1) return 0;
    while (t--) {
        int n, a[512]; scanf("%d", &n);
        for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
        printf("%d\n", solver(a, n));
    }
    return 0;
}
