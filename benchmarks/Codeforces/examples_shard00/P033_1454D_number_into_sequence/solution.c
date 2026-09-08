/* Codeforces 1454/D - Number into Sequence */
#include <stdio.h>

static int solver(long long n, long long *out)
{
    long long value = n, best_prime = n; int best_exp = 1;
    for (long long p = 2; p * p <= value; ++p) if (value % p == 0) {
        int e = 0; while (value % p == 0) { value /= p; ++e; }
        if (e > best_exp) { best_exp = e; best_prime = p; }
    }
    long long rest = n;
    for (int i = 0; i + 1 < best_exp; ++i) { out[i] = best_prime; rest /= best_prime; }
    out[best_exp - 1] = rest;
    return best_exp;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        long long n, out[64]; scanf("%lld", &n);
        int count = solver(n, out); printf("%d\n", count);
        for (int i = 0; i < count; ++i) printf("%lld%c", out[i], i + 1 == count ? '\n' : ' ');
    }
    return 0;
}
