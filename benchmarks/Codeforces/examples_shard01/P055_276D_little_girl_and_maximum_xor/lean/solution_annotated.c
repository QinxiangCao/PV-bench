/*@ Import Lean
import Codeforces.examples_shard01.P055_276D_little_girl_and_maximum_xor.lean.helper_lib
open scoped SimpleC
*/
/*
 * Codeforces 276/D - Little Girl and Maximum XOR  (rating 1700, BITMASKS)
 *
 * Let b be the highest bit where l and r differ.  Then [l, r] contains a
 * number with bit b clear and all lower bits set, and one with bit b set and
 * all lower bits clear, so every bit up to b can be made 1: the answer is
 * 2^(b+1) - 1 (and 0 when l == r).
 */

// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (HighestBitScan : Z -> Z -> Z -> Z -> Prop)
*/

/* solver: pure.  Maximum a xor b over l <= a <= b <= r. */
static unsigned long long solver(unsigned long long l, unsigned long long r)
/*@
    Require
      1 <= l && l <= r && r <= 1000000000000000000 &&
      emp
    Ensure
      Spec(l, r, __return) &&
      emp
*/
{
    unsigned long long x = l ^ r;
    if (x == 0)
        return 0;
    int b = 63;
    /*@ Inv Assert
          l == l@pre && r == r@pre &&
          1 <= l@pre && l@pre <= r@pre &&
          r@pre <= 1000000000000000000 &&
          0 < x && x <= 18446744073709551615 &&
          0 <= b && b <= 63 &&
          HighestBitScan(l@pre, r@pre, x, b) &&
          emp
    */
    while (!((x >> b) & 1ULL))
        b--;
    return (b == 63) ? ~0ULL : ((1ULL << (b + 1)) - 1);
}

// int main(void)
// {
//     unsigned long long l, r;
//     if (scanf("%llu %llu", &l, &r) != 2)
//         return 0;
//     printf("%llu\n", solver(l, r));
//     return 0;
// }
