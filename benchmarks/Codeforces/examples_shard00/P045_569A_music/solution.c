/* Codeforces 569/A - Music */
#include <stdio.h>

static int solver(long long t, long long s, long long q)
{
    int starts = 0; while (s < t) { s *= q; ++starts; } return starts;
}

int main(void)
{
    long long t, s, q; if (scanf("%lld %lld %lld", &t, &s, &q) != 3) return 0;
    printf("%d\n", solver(t, s, q));
    return 0;
}
