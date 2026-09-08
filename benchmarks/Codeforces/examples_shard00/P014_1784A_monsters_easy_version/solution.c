/* Codeforces 1784/A - Monsters (easy version) */
#include <stdio.h>
#include <stdlib.h>

static int cmp_int(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}

static long long solver(int *a, int n)
{
    qsort(a, (size_t)n, sizeof(*a), cmp_int);
    long long spent = 0;
    int kept = 0;
    for (int i = 0; i < n; ++i) {
        int next = kept + 1;
        if (next > a[i]) next = a[i];
        spent += a[i] - next;
        kept = next;
    }
    return spent;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, *a; scanf("%d", &n); a = malloc((size_t)n * sizeof(*a));
        for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
        printf("%lld\n", solver(a, n)); free(a);
    }
    return 0;
}
