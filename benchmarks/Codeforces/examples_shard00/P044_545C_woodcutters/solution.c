/* Codeforces 545/C - Woodcutters */
#include <stdio.h>
#include <stdlib.h>

static int solver(const long long *x, const long long *h, int n)
{
    if (n <= 2) return n;
    int answer = 2; long long occupied = x[0];
    for (int i = 1; i + 1 < n; ++i) {
        if (x[i] - h[i] > occupied) { ++answer; occupied = x[i]; }
        else if (x[i] + h[i] < x[i + 1]) { ++answer; occupied = x[i] + h[i]; }
        else occupied = x[i];
    }
    return answer;
}

int main(void)
{
    int n; if (scanf("%d", &n) != 1) return 0;
    long long *x = malloc((size_t)n * sizeof(*x)), *h = malloc((size_t)n * sizeof(*h));
    for (int i = 0; i < n; ++i) scanf("%lld %lld", &x[i], &h[i]);
    printf("%d\n", solver(x, h, n)); free(x); free(h);
    return 0;
}
