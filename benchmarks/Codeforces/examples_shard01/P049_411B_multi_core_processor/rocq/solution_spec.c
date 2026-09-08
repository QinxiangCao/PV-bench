/*
 * Codeforces 411/B - Multi-core Processor  (rating 1600, IMPLEMENTATION)
 *
 * Simulate cycle by cycle: within a cycle, count the live cores addressing
 * each cell.  A cell with two or more writers locks (with its writers), and a
 * write to an already locked cell locks that single core.
 */

// #include <stdio.h>
// #include <string.h>
#include "array2_ext_def.h"
static void *memset(void *dst, int c, unsigned long n)
/*@ Require
      0 <= n && c == 0 && 
      UCharArray::undef_full(dst, n)
    Ensure
      __return == dst && 
      UCharArray::full(dst, n, repeat_Z(0, n))
*/;


#define MAXN 105

/* solver: pure.  x[i][j] instructions -> lock[i] = locking cycle or 0. */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P049_411B_multi_core_processor.rocq.spec_lib */
/*@ Extern Coq
      (Pre : Z -> list(list Z) -> Prop)
      (Spec : Z -> list(list Z) -> list Z -> Prop)
      (concat : {A} -> list (list A) -> list A)
*/
static void solver(int n, int m, int k, const int x[][MAXN], int *lock)
/*@ With (ins : list(list Z)) (xrows : list(list Z))
    Require
      1 <= k && k <= 100 &&
      Pre(k, ins) && 1 <= n && n <= 100 && 1 <= m && m <= 100 && (forall j, (0 <= j && j < n * m) => (0 <= concat(ins)[j] && concat(ins)[j] <= k)) &&
      n == Zlength(ins) && (forall i, (0 <= i && i < n) => Zlength(ins[i]) == m) && Zlength(xrows) == n && (forall i, (0 <= i && i < n) => (Zlength(xrows[i]) == 105 && sublist(0, m, xrows[i]) == ins[i])) && IntArray2::full(x, n, 105, xrows) * IntArray::undef_full(lock, n)
    Ensure
      exists (out : list Z),
        Spec(k@pre, ins, out) &&
        Zlength(out) == n && IntArray2::full(x, n, 105, xrows) * IntArray::full(lock, n, out)
*/
{
    int cell_locked[MAXN] = {0};
    int writers[MAXN], first[MAXN];
    for (int i = 0; i < n; i++)
        lock[i] = 0;
    for (int j = 0; j < m; j++) {
        memset(writers, 0, sizeof(int) * (k + 1));
        for (int c = 1; c <= k; c++)
            first[c] = -1;
        for (int i = 0; i < n; i++) {
            if (lock[i] || x[i][j] == 0)
                continue;
            int c = x[i][j];
            if (cell_locked[c]) {
                lock[i] = j + 1;           /* writing to a dead cell */
                continue;
            }
            writers[c] = writers[c] + 1;
            if (first[c] < 0)
                first[c] = i;
        }
        for (int c = 1; c <= k; c++)
            if (writers[c] >= 2) {
                cell_locked[c] = 1;
                for (int i = 0; i < n; i++)
                    if (!lock[i] && x[i][j] == c)
                        lock[i] = j + 1;
            }
    }
}

// int main(void)
// {
//     int n, m, k;
//     if (scanf("%d %d %d", &n, &m, &k) != 3)
//         return 0;
//     static int x[MAXN][MAXN], lock[MAXN];
//     for (int i = 0; i < n; i++)
//         for (int j = 0; j < m; j++)
//             scanf("%d", &x[i][j]);
//     solver(n, m, k, x, lock);
//     for (int i = 0; i < n; i++)
//         printf("%d\n", lock[i]);
//     return 0;
// }
