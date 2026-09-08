/* Codeforces 1903/C - Theofanis' Nightmare */
#include <stdio.h>
#include <stdlib.h>

static long long solver(const long long *a, int n)
{
    long long suffix = 0, answer = 0;
    for (int i = n - 1; i >= 0; --i) {
        suffix += a[i];
        if (i == 0 || suffix > 0) answer += suffix;
    }
    return answer;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; scanf("%d", &n); long long *a = malloc((size_t)n * sizeof(*a));
        for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
        printf("%lld\n", solver(a, n)); free(a);
    }
    return 0;
}
