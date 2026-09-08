/* Codeforces 1113/B - Sasha and Magnetic Machines */
#include <stdio.h>

static int solver(const int *a, int n)
{
    int mn = 101, sum = 0;
    for (int i = 0; i < n; ++i) { sum += a[i]; if (a[i] < mn) mn = a[i]; }
    int answer = sum;
    for (int i = 0; i < n; ++i) for (int x = 2; x <= a[i]; ++x) {
        if (a[i] % x) continue;
        int candidate = sum - a[i] - mn + a[i] / x + mn * x;
        if (candidate < answer) answer = candidate;
    }
    return answer;
}

int main(void)
{
    int n, a[50000];
    if (scanf("%d", &n) != 1) return 0;
    for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
    printf("%d\n", solver(a, n));
    return 0;
}
