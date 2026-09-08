/* Codeforces 440/B - Balancer */
#include <stdio.h>

static long long solver(const long long *a, int n)
{
    long long sum = 0; for (int i = 0; i < n; ++i) sum += a[i];
    long long target = sum / n, balance = 0, answer = 0;
    for (int i = 0; i + 1 < n; ++i) { balance += a[i] - target; answer += balance < 0 ? -balance : balance; }
    return answer;
}

int main(void)
{
    int n; if (scanf("%d", &n) != 1) return 0;
    long long a[50000]; for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
    printf("%lld\n", solver(a, n));
    return 0;
}
