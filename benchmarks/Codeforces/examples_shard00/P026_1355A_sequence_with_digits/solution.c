/* Codeforces 1355/A - Sequence with Digits */
#include <stdio.h>

static long long step(long long x)
{
    int mn = 9, mx = 0;
    while (x) {
        int d = (int)(x % 10); x /= 10;
        if (d < mn) mn = d;
        if (d > mx) mx = d;
    }
    return (long long)mn * mx;
}

static long long solver(long long a, long long k)
{
    for (long long i = 1; i < k; ++i) {
        long long add = step(a);
        if (!add) break;
        a += add;
    }
    return a;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        long long a, k; scanf("%lld %lld", &a, &k);
        printf("%lld\n", solver(a, k));
    }
    return 0;
}
