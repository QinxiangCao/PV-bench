/* Codeforces 1771/C - Hossam and Trainees */
#include <stdio.h>
#include <stdlib.h>

static int cmp_int(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}

static int solver(const int *values, int n)
{
    static int primes[4000]; int pc = 0; unsigned char composite[31624] = {0};
    for (int i = 2; i <= 31623; ++i)
        if (!composite[i]) { primes[pc++] = i; if ((long long)i * i <= 31623) for (int j = i * i; j <= 31623; j += i) composite[j] = 1; }
    int *factors = malloc((size_t)n * 10 * sizeof(*factors)); int count = 0;
    for (int i = 0; i < n; ++i) {
        int x = values[i];
        for (int j = 0; j < pc && (long long)primes[j] * primes[j] <= x; ++j) if (x % primes[j] == 0) {
            factors[count++] = primes[j]; while (x % primes[j] == 0) x /= primes[j];
        }
        if (x > 1) factors[count++] = x;
    }
    qsort(factors, (size_t)count, sizeof(*factors), cmp_int);
    int ok = 0; for (int i = 1; i < count; ++i) if (factors[i] == factors[i - 1]) ok = 1;
    free(factors); return ok;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; scanf("%d", &n); int *values = malloc((size_t)n * sizeof(*values));
        for (int i = 0; i < n; ++i) scanf("%d", &values[i]);
        puts(solver(values, n) ? "YES" : "NO"); free(values);
    }
    return 0;
}
