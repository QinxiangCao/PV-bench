/*
 * Codeforces 1538/F - Interesting Function  (rating 1500, MATH)
 *
 * Going from 0 to x, the last digit changes on every step, the tens digit on
 * every tenth step, and so on, so the total number of changed digits is
 * sum_d floor(x / 10^d).  The answer is that count for r minus the one for l.
 */

#include <stdio.h>

/* solver: pure.  Total digits changed while counting from 0 up to x. */
static long long changed_upto(long long x)
{
    long long total = 0;
    for (long long p = 1; p <= x; p *= 10)
        total += x / p;
    return total;
}

/* solver: complete interval case. */
static long long solver(long long l, long long r)
{
    return changed_upto(r) - changed_upto(l);
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    while (t--) {
        long long l, r;
        scanf("%lld %lld", &l, &r);
        printf("%lld\n", solver(l, r));
    }
    return 0;
}
