/*
 * Codeforces 1288/D - Minimax Problem  (rating 2000, BINARY SEARCH)
 *
 * Binary search the answer x.  Each array becomes an m-bit mask marking the
 * positions where it reaches x; the pair works iff the two masks cover all m
 * positions.  With m <= 8 there are only 256 masks, so keep one representative
 * of each and test all pairs.
 */

// #include <stdio.h>
#include "array2_ext_def.h"

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P066_1288D_minimax_problem.rocq.spec_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Pre : list(list Z) -> Prop)
      (concat : {A} -> list (list A) -> list A)
      (Spec : list(list Z) -> Z*Z -> Prop)
*/

/* feasible: is some pair of arrays >= x in every position?  Stores the winning
 * indices in *bi, *bj. */
static int feasible(const int *a, int n, int m, int x, int *rep, int *bi, int *bj)
{
    int full = (1 << m) - 1;
    for (int s = 0; s <= full; s++)
        rep[s] = -1;
    for (int i = 0; i < n; i++) {
        int mask = 0;
        for (int j = 0; j < m; j++)
            if (a[i * m + j] >= x)
                mask |= 1 << j;
        if (rep[mask] < 0)
            rep[mask] = i;
    }
    for (int s = 0; s <= full; s++) {
        if (rep[s] < 0)
            continue;
        for (int u = 0; u <= full; u++)
            if (rep[u] >= 0 && (s | u) == full) {
                *bi = rep[s] + 1;
                *bj = rep[u] + 1;
                return 1;
            }
    }
    return 0;
}

/* solver: indices maximising min_k max(a_i[k], a_j[k]). */
static void solver(const int *a, int n, int m, int *rep, int *bi, int *bj)
/*@ With (rows : list(list Z))
    Require
      Pre(rows) && 1 <= n && n <= 300000 && (forall i, (0 <= i && i < n) => (1 <= m && m <= 8)) && (forall k, (0 <= k && k < n * m) => (0 <= concat(rows)[k] && concat(rows)[k] <= 1000000000)) &&
      n == Zlength(rows) && m == Zlength(rows[0]) && IntArray2::full(a, n, m, rows) * IntArray::full_shape(rep, 256) * IntArray::undef_full(bi, 1) * IntArray::undef_full(bj, 1)
    Ensure
      exists (out : Z*Z),
        Spec(rows, out) &&
        IntArray2::full(a, n, m, rows) * IntArray::full_shape(rep, 256) * IntArray::full(bi, 1, cons(fst(out), nil)) * IntArray::full(bj, 1, cons(snd(out), nil))
*/
{
    int lo = 0, hi = 1000000000;
    *bj = 1;
    *bi = *bj;
    while (lo < hi) {
        int mid = lo + (hi - lo + 1) / 2;
        int ci, cj;
        if (feasible(a, n, m, mid, rep, &ci, &cj)) {
            lo = mid;
            *bi = ci;
            *bj = cj;
        } else {
            hi = mid - 1;
        }
    }
    if (lo == 0)
        feasible(a, n, m, 0, rep, bi, bj);
}

// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     static int a[300005 * 8], rep[256];
//     for (int i = 0; i < n * m; i++)
//         scanf("%d", &a[i]);
//     int bi, bj;
//     solver(a, n, m, rep, &bi, &bj);
//     printf("%d %d\n", bi, bj);
//     return 0;
// }
