/*
 * Codeforces 1313/A - Fast Food Restaurant  (rating 900, BRUTE FORCE)
 *
 * There are only 7 possible non-empty dish sets, so try every subfamily of
 * them (2^7 = 128) and keep the largest one whose total demand for each dish
 * fits the stock.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P007_1313A_fast_food_restaurant.rocq.spec_lib */

/* solver: pure.  Maximum number of visitors servable from a, b, c portions. */
static int solver(int a, int b, int c)
/*@
    Require
      0 <= a && a <= 10 && 0 <= b && b <= 10 && 0 <= c && c <= 10 &&
      emp
    Ensure
      Spec(a, b, c, __return) &&
      emp
*/
{
    int best = 0;
    for (int fam = 0; fam < 128; fam++) {
        int need[3] = {0, 0, 0}, cnt = 0;
        for (int s = 1; s <= 7; s++)
            if (fam & (1 << (s - 1))) {
                cnt++;
                for (int d = 0; d < 3; d++)
                    if (s & (1 << d))
                        need[d]++;
            }
        if (need[0] <= a && need[1] <= b && need[2] <= c && cnt > best)
            best = cnt;
    }
    return best;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int a, b, c;
//         scanf("%d %d %d", &a, &b, &c);
//         printf("%d\n", solver(a, b, c));
//     }
//     return 0;
// }

