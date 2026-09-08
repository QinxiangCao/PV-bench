/*
 * Codeforces 1737/B - Ela's Fitness and the Luxury Number  (rating 1300, MATH)
 *
 * For s = floor(sqrt(x)), the luxurious numbers with that same s are exactly
 * s^2, s^2+s and s^2+2s.  So counting up to x gives 3*(s-1) complete blocks
 * below s, plus however many of those three do not exceed x.
 */

// #include <stdio.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P033_1737B_elas_fitness_and_the_luxury_number.rocq.spec_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/

/* isqrt: floor(sqrt(v)) for 0 <= v <= 1e18.  Binary search on the answer keeps
 * this in integers -- no math.h, and no double-rounding to correct for.  The
 * test is written as mid <= v / mid rather than mid * mid <= v, which would
 * overflow for mid above 3e9. */
static long long isqrt(long long v)
{
    long long lo = 0, hi = 2000000000LL;  /* 2e9 > sqrt(1e18) = 1e9 */
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;   /* mid >= 1, so v / mid is safe */
        if (mid <= v / mid)
            lo = mid;
        else
            hi = mid - 1;
    }
    return lo;
}

/* solver: pure.  Count of luxurious numbers in [1, x]. */
static long long count_upto(long long x)
{
    if (x <= 0)
        return 0;
    long long s = isqrt(x), cnt = 3 * (s - 1);
    long long base = s * s;
    for (int m = 0; m < 3; m++)
        if (base + m * s <= x)
            cnt++;
    return cnt;
}

/* solver: complete interval case. */
static long long solver(long long l, long long r)
/*@ Require
      1 <= l && l <= r && r <= 1000000000000000000 &&
      emp
    Ensure
      Spec(l, r, __return) && emp
*/
{
    return count_upto(r) - count_upto(l - 1);
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         long long l, r;
//         scanf("%lld %lld", &l, &r);
//         printf("%lld\n", solver(l, r));
//     }
//     return 0;
// }
