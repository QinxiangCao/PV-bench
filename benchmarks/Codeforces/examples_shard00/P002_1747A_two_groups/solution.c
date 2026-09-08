/* Codeforces 1747/A - Two Groups */
#include <stdio.h>
#include <stdlib.h>

static long long solver(const long long *a, int n)
{
    long long sum = 0;
    for (int i = 0; i < n; ++i) sum += a[i];
    return llabs(sum);
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1) return 0;
    while (t--) {
        int n; long long a[100005];
        scanf("%d", &n);
        for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
        printf("%lld\n", solver(a, n));
    }
    return 0;
}
