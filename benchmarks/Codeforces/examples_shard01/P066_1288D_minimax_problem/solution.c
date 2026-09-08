/*
 * Codeforces 1288/D - Minimax Problem  (rating 2000, BINARY SEARCH)
 *
 * Binary search the answer x.  Each array becomes an m-bit mask marking the
 * positions where it reaches x; the pair works iff the two masks cover all m
 * positions.  With m <= 8 there are only 256 masks, so keep one representative
 * of each and test all pairs.
 */

#include <stdio.h>

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

int main(void)
{
    int n, m;
    if (scanf("%d %d", &n, &m) != 2)
        return 0;
    static int a[300005 * 8], rep[256];
    for (int i = 0; i < n * m; i++)
        scanf("%d", &a[i]);
    int bi, bj;
    solver(a, n, m, rep, &bi, &bj);
    printf("%d %d\n", bi, bj);
    return 0;
}
