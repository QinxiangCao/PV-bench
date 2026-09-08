/*
 * Codeforces 412/A - Poster  (rating 900, GREEDY)
 *
 * Every square must be painted, so the ladder has to visit all n positions;
 * the cheapest route walks to the nearer end first and then sweeps across.
 * Cost = (n-1) sweep steps + min(k-1, n-k) steps to reach that end + n prints.
 */

// #include <stdio.h>
#include "array2_ext_def.h"

/*@ Extern Coq
      (Spec : Z -> list Z -> list (Z*Z) -> Prop)
      (SolverOutputBridge : Z -> list (Z*Z) -> Z -> list(list Z) -> list(list Z) -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P010_412A_poster.rocq.spec_lib */

static void write_left(char dst[8])
{
    dst[0] = 'L';
    dst[1] = 'E';
    dst[2] = 'F';
    dst[3] = 'T';
    dst[4] = '\0';
}

static void write_right(char dst[8])
{
    dst[0] = 'R';
    dst[1] = 'I';
    dst[2] = 'G';
    dst[3] = 'H';
    dst[4] = 'T';
    dst[5] = '\0';
}

static void write_print(char dst[8], char ch)
{
    dst[0] = 'P';
    dst[1] = 'R';
    dst[2] = 'I';
    dst[3] = 'N';
    dst[4] = 'T';
    dst[5] = ' ';
    dst[6] = ch;
    dst[7] = '\0';
}

/* solver: pure.  Writes the optimal plan into out[] as one action per row
 * ("LEFT", "RIGHT" or "PRINT x") and returns the number of actions. */
static int solver(const char *s, int n, int k, char out[][8])
/*@ With (cursor : Z) (text : list Z) (out_before : list(list Z))
    Require
      1 <= k && k <= n && 1 <= n && n <= 100 &&
      (forall i, (0 <= i && i < n) =>
        ((65 <= text[i] && text[i] <= 90) ||
         (48 <= text[i] && text[i] <= 57) ||
         text[i] == 46 || text[i] == 33 || text[i] == 44 || text[i] == 63)) &&
      n == Zlength(text) && k == cursor && Zlength(out_before) == 3 * n &&
      (forall i, (0 <= i && i < 3 * n) => Zlength(out_before[i]) == 8) && CharArray::full(s, n, text) * CharArray2::full(out, 3 * n, 8, out_before)
    Ensure
      exists (out_spec : list (Z*Z)) (out_after : list(list Z)),
        Spec(cursor, text, out_spec) &&
        SolverOutputBridge(3 * n, out_spec, __return, out_before, out_after) && CharArray::full(s, n, text) * CharArray2::full(out, 3 * n, 8, out_after)
*/
{
    int t = 0;
    if (k - 1 <= n - k) {                     /* walk left, then sweep right */
        for (int p = k; p > 1; p--)
            {
                write_left(out[t]);
                t++;
            }
        for (int p = 1; p <= n; p++) {
            write_print(out[t], s[p - 1]);
            t++;
            if (p < n)
                {
                    write_right(out[t]);
                    t++;
                }
        }
    } else {                                  /* walk right, then sweep left */
        for (int p = k; p < n; p++)
            {
                write_right(out[t]);
                t++;
            }
        for (int p = n; p >= 1; p--) {
            write_print(out[t], s[p - 1]);
            t++;
            if (p > 1)
                {
                    write_left(out[t]);
                    t++;
                }
        }
    }
    return t;
}

// int main(void)
// {
//     int n, k;
//     if (scanf("%d %d", &n, &k) != 2)
//         return 0;
//     static char s[105];
//     scanf("%104s", s);
//     static char out[305][8];
//     int t = solver(s, n, k, out);
//     for (int i = 0; i < t; i++)
//         puts(out[i]);
//     return 0;
// }
