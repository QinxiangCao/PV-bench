/* Codeforces 1537/B - Bad Boy */
#include <stdio.h>

static void solver(long long n, long long m, long long i, long long j,
                   long long out[4])
{
    (void)i; (void)j;
    out[0] = 1; out[1] = 1; out[2] = n; out[3] = m;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        long long n, m, i, j;
        scanf("%lld %lld %lld %lld", &n, &m, &i, &j);
        long long out[4]; solver(n, m, i, j, out);
        printf("%lld %lld %lld %lld\n", out[0], out[1], out[2], out[3]);
    }
    return 0;
}
