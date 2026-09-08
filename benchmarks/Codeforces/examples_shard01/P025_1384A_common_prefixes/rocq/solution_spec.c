/*
 * Codeforces 1384/A - Common Prefixes  (rating 1200, CONSTRUCTIVE)
 *
 * Keep one working string of 200 letters.  To realise a_i, copy the current
 * string and flip the letter at index a_i between 'a' and 'b': the first a_i
 * letters still agree and position a_i now differs, so the longest common
 * prefix is exactly a_i (a_i <= 50 < 200, so the index always exists).
 */

// #include <stdio.h>
#include "array2_ext_def.h"
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P025_1384A_common_prefixes.rocq.spec_lib */
/*@ Extern Coq
      (Spec : list Z -> list(list Z) -> Prop)
*/

#define LEN 200

/* solver: pure.  Writes n+1 strings of length LEN into out[][], consecutive
 * ones having longest common prefix a[i]. */
static void solver(const int *a, int n, char out[][LEN + 1])
/*@ With (prefix_lengths : list Z)
    Require
      1 <= n && n <= 100 && (forall i, (0 <= i && i < n) => (0 <= prefix_lengths[i] && prefix_lengths[i] <= 50)) &&
      n == Zlength(prefix_lengths) && IntArray::full(a, n, prefix_lengths) * CharArray2::undef_full(out, n + 1, 201)
    Ensure
      exists (out_spec : list(list Z)),
        Spec(prefix_lengths, out_spec) &&
        Zlength(out_spec) == n + 1 && (forall i, (0 <= i && i < n + 1) => Zlength(out_spec[i]) == 200) && exists (out_rows : list(list Z)), Zlength(out_rows) == n + 1 && (forall i, (0 <= i && i < n + 1) => out_rows[i] == app(out_spec[i], cons(0, nil))) && IntArray::full(a, n, prefix_lengths) * CharArray2::full(out, n + 1, 201, out_rows)
*/
{
    for (int j = 0; j < LEN; j++)
        out[0][j] = 'a';
    out[0][LEN] = '\0';
    for (int i = 0; i < n; i++) {
        for (int j = 0; j <= LEN; j++)
            out[i + 1][j] = out[i][j];
        int k = a[i];
        out[i + 1][k] = out[i][k] == 'a' ? 'b' : 'a';
    }
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[105];
//     static char out[106][LEN + 1];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         solver(a, n, out);
//         for (int i = 0; i <= n; i++)
//             puts(out[i]);
//     }
//     return 0;
// }
