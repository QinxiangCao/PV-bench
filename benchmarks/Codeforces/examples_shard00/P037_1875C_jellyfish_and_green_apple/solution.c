/* Codeforces 1875/C - Jellyfish and Green Apple */
#include <stdio.h>

static long long gcdll(long long a, long long b)
{
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long solver(long long n, long long m)
{
    long long d = m / gcdll(n, m);
    if (d & (d - 1)) return -1;
    n %= m;
    long long answer = 0;
    while (n) { answer += n; n = (2 * n) % m; }
    return answer;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) { long long n, m; scanf("%lld %lld", &n, &m); printf("%lld\n", solver(n, m)); }
    return 0;
}
