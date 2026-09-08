/*
 * Codeforces 474/B - Worms  (rating 1200, BINARY SEARCH)
 *
 * Prefix sums give each pile's last label; a binary search over them maps a
 * queried label to its pile.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P028_474B_worms.rocq.spec_lib */

/* solver: pure.  Index (1-based) of the pile holding label q, given the
 * prefix sums pre[1..n] of the pile sizes. */
static int locate_pile(const long long *pre, int n, long long q)
{
    int lo = 1, hi = n;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (pre[mid] >= q)
            hi = mid;
        else
            lo = mid + 1;
    }
    return lo;
}

/* solver: complete case.  Build prefix sums and answer the whole query list. */
static void solver(const int *piles, int n, const long long *queries, int m,
                   int *out, long long *pre)
/*@ With (pile_sizes : list Z) (worm_queries : list Z)
    Require
      1 <= n && n <= 100000 && 1 <= m && m <= 100000 &&
      (forall i, (0 <= i && i < n) => (1 <= pile_sizes[i] && pile_sizes[i] <= 1000)) &&
      (forall i, (0 <= i && i < m) => 1 <= worm_queries[i]) &&
      Pre(pile_sizes, worm_queries) && n == Zlength(pile_sizes) && m == Zlength(worm_queries) && IntArray::full(piles, n, pile_sizes) * Int64Array::full(queries, m, worm_queries) * IntArray::full_shape(out, m) * Int64Array::full_shape(pre, n + 1)
    Ensure
      exists (result : list Z), Spec(pile_sizes, worm_queries, result) && IntArray::full(piles, n, pile_sizes) * Int64Array::full(queries, m, worm_queries) * IntArray::full(out, m, result) * Int64Array::full_shape(pre, n + 1)
*/
{
    pre[0] = 0;
    for (int i = 0; i < n; i++) {
        pre[i + 1] = pre[i] + piles[i];
    }
    for (int i = 0; i < m; i++) {
        out[i] = locate_pile(pre, n, queries[i]);
    }
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int piles[100005], out[100005];
//     static long long pre[100005], queries[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &piles[i]);
//     int m;
//     scanf("%d", &m);
//     for (int i = 0; i < m; i++)
//         scanf("%lld", &queries[i]);
//     solver(piles, n, queries, m, out, pre);
//     for (int i = 0; i < m; i++)
//         printf("%d\n", out[i]);
//     return 0;
// }
