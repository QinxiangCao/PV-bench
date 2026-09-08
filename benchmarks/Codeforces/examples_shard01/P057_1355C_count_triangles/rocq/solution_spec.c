/*
 * Codeforces 1355/C - Count Triangles  (rating 1800, MATH)
 *
 * With A <= x <= B <= y <= C <= z <= D the only binding triangle inequality is
 * x + y > z.  Group the pairs by their sum s = x + y (at most 1e6 values):
 * the number of pairs with that sum is a simple interval intersection, and
 * each admits every z in [C, min(D, s-1)].
 */

// #include <stdio.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P057_1355C_count_triangles.rocq.spec_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Z -> Prop)
*/

/* solver: pure.  Number of non-degenerate triangles in the given ranges. */
static long long solver(long long A, long long B, long long C, long long D)
/*@
    Require
      1 <= A && A <= B && B <= C && C <= D && D <= 500000 &&
      emp
    Ensure
      Spec(A, B, C, D, __return) &&
      emp
*/
{
    long long total = 0;
    for (long long s = A + B; s <= B + C; s++) {
        long long xlo = A > s - C ? A : s - C;     /* x >= A and y = s-x <= C */
        long long xhi = B < s - B ? B : s - B;     /* x <= B and y = s-x >= B */
        if (xlo > xhi)
            continue;
        long long pairs = xhi - xlo + 1;
        long long zhi = D < s - 1 ? D : s - 1;
        if (zhi < C)
            continue;
        total += pairs * (zhi - C + 1);
    }
    return total;
}

// int main(void)
// {
//     long long A, B, C, D;
//     if (scanf("%lld %lld %lld %lld", &A, &B, &C, &D) != 4)
//         return 0;
//     printf("%lld\n", solver(A, B, C, D));
//     return 0;
// }
