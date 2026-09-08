/* Codeforces 303/A - Lucky Permutation Triple */
#include <stdio.h>
#include <stdlib.h>

static int solver(int n, int *out)
{
    if ((n & 1) == 0) return 0;
    for (int i = 0; i < n; ++i) out[i] = i;
    for (int i = 0; i < n; ++i) out[n + i] = i;
    for (int i = 0; i < n; ++i) out[2 * n + i] = 2 * i % n;
    return 1;
}

int main(void)
{
    int n; if (scanf("%d", &n) != 1) return 0;
    int *out = malloc((size_t)3 * n * sizeof(*out));
    if (!solver(n, out)) { puts("-1"); free(out); return 0; }
    for (int row = 0; row < 3; ++row)
        for (int i = 0; i < n; ++i) printf("%d%c", out[row * n + i], i + 1 == n ? '\n' : ' ');
    free(out); return 0;
}
