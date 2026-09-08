/* Codeforces 630/I - Parking Lot */
#include <stdio.h>

static long long power4(int e)
{
    long long r = 1;

    while (e > 0)
    {
        r *= 4;
        e -= 1;
    }

    return r;
}

static long long solver(int n)
{
    long long first = power4(n - 3);
    long long second = power4(n - 4);

    return 24 * first + (long long)(n - 3) * 36 * second;
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    printf("%lld\n", solver(n));
    return 0;
}
