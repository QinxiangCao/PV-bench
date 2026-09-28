/* Codeforces 1102/A - Integer Sequence Dividing */
#include <stdio.h>

static long long solver(long long n)
{
    return (n * (n + 1) / 2) & 1LL;
}

int main(void)
{
    long long n;
    if (scanf("%lld", &n) == 1) printf("%lld\n", solver(n));
    return 0;
}
