/*@ Import Lean
import Codeforces.examples_shard01.P022_705B_spider_man.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 705/B - Spider Man  (rating 1100, GAMES)
 *
 * Every move splits one cycle in two, leaving the vertex count alone and
 * raising the cycle count by one.  The game ends when all cycles are single
 * vertices, so the number of moves is exactly (total vertices) - (number of
 * cycles), no matter how anyone plays: the first player wins iff that is odd.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : list Z -> list Z -> Prop)
*/
/* solver: pure.  Parity state after adding a cycle of a vertices to a set
 * whose (vertices - cycles) parity is par; returns the new parity. */
static int next_parity(int par, long long a)
{
    return (int)((par + (a - 1)) & 1);
}

/* solver: complete case.  Produce the answer after every added cycle. */
static void solver(const long long *added, int n, int *out)
/*@ With (added_values : list Z)
    Require
      1 <= n && n <= 100000 &&
      (forall i, (0 <= i && i < n) => (1 <= added_values[i] && added_values[i] <= 1000000000)) && n == Zlength(added_values) && Int64Array::full(added, n, added_values) * IntArray::full_shape(out, n)
    Ensure
      exists (result : list Z), Spec(added_values, result) && Int64Array::full(added, n, added_values) * IntArray::full(out, n, result)
*/
{
    int par = 0;
    for (int i = 0; i < n; i++) {
        par = next_parity(par, added[i]);
        out[i] = par ? 1 : 2;
    }
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static long long added[100005];
//     static int out[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%lld", &added[i]);
//     solver(added, n, out);
//     for (int i = 0; i < n; i++)
//         printf("%d\n", out[i]);
//     return 0;
// }
