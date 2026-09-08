/*
 * Codeforces 275/A - Lights Out  (rating 900, IMPLEMENTATION)
 *
 * Only the parity of each press count matters.  A light ends up on iff it was
 * toggled an even number of times, i.e. the sum of presses on itself and its
 * four side-adjacent cells is even (all lights start on).
 */

// #include <stdio.h>
#include "array2_ext_def.h"
/*@ Extern Coq
      (Spec : list (list Z) -> list (list Z) -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P009_275A_lights_out.rocq.spec_lib */

/* solver: pure.  press[3][3] press counts -> out[3][3] final states 0/1. */
static void solver(const int press[3][3], int out[3][3])
/*@ With (g : list (list Z))
    Require
      Zlength(g) == 3 && (forall i, (0 <= i && i < 3) => Zlength(g[i]) == 3) && (forall i, (0 <= i && i < 3) => (forall k, (0 <= k && k < 3) => (0 <= g[i][k] && g[i][k] <= 100))) &&
      IntArray2::full(press, 3, 3, g) * IntArray2::undef_full(out, 3, 3)
    Ensure
      exists (out_spec : list (list Z)),
        Spec(g, out_spec) &&
        IntArray2::full(press, 3, 3, g) * IntArray2::full(out, 3, 3, out_spec)
*/
{
    const int di[5] = {0, -1, 1, 0, 0};
    const int dj[5] = {0, 0, 0, -1, 1};
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            int tog = 0;
            for (int d = 0; d < 5; d++) {
                int ni = i + di[d], nj = j + dj[d];
                if (ni >= 0 && ni < 3 && nj >= 0 && nj < 3)
                    tog += press[ni][nj];
            }
            out[i][j] = (tog % 2 == 0);       /* started on */
        }
}

// int main(void)
// {
//     int press[3][3], out[3][3];
//     for (int i = 0; i < 3; i++)
//         for (int j = 0; j < 3; j++)
//             if (scanf("%d", &press[i][j]) != 1)
//                 return 0;
//     solver(press, out);
//     for (int i = 0; i < 3; i++) {
//         for (int j = 0; j < 3; j++)
//             putchar('0' + out[i][j]);
//         putchar('\n');
//     }
//     return 0;
// }
