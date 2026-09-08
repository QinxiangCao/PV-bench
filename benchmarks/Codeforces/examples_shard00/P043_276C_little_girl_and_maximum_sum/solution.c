/* Codeforces 276/C - Little Girl and Maximum Sum */
#include <stdio.h>
#include <stdlib.h>

static int cmp_ll(const void *x, const void *y)
{
    long long a = *(const long long *)x, b = *(const long long *)y;
    return (a > b) - (a < b);
}

static long long solver(long long *a, int n, const int *left, const int *right, int q)
{
    long long *diff = calloc((size_t)n + 1, sizeof(*diff));
    for (int i = 0; i < q; ++i) { ++diff[left[i] - 1]; --diff[right[i]]; }
    for (int i = 1; i < n; ++i) diff[i] += diff[i - 1];
    qsort(a, (size_t)n, sizeof(*a), cmp_ll); qsort(diff, (size_t)n, sizeof(*diff), cmp_ll);
    long long answer = 0; for (int i = 0; i < n; ++i) answer += a[i] * diff[i];
    free(diff); return answer;
}

int main(void)
{
    int n, q; if (scanf("%d %d", &n, &q) != 2) return 0;
    long long *a = malloc((size_t)n * sizeof(*a));
    int *left = malloc((size_t)q * sizeof(*left)), *right = malloc((size_t)q * sizeof(*right));
    for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
    for (int i = 0; i < q; ++i) scanf("%d %d", &left[i], &right[i]);
    printf("%lld\n", solver(a, n, left, right, q)); free(a); free(left); free(right);
    return 0;
}
