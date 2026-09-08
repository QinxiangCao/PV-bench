/* Codeforces 1807/G2 - Subsequence Addition (Hard Version) */
#include <stdio.h>
#include <stdlib.h>

static int cmp_int(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}

static int solver(int *a, int n)
{
    qsort(a, (size_t)n, sizeof(*a), cmp_int);
    if (a[0] != 1) return 0;
    long long sum = 1;
    for (int i = 1; i < n; ++i) {
        if (a[i] > sum) return 0;
        sum += a[i];
    }
    return 1;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, *a; scanf("%d", &n); a = malloc((size_t)n * sizeof(*a));
        for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
        puts(solver(a, n) ? "YES" : "NO"); free(a);
    }
    return 0;
}
