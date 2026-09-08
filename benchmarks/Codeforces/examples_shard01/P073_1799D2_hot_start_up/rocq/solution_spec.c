/*
 * Codeforces 1799/D2 - Hot Start Up (hard version)  (rating 2100, DP)
 *
 * After running a_i, one CPU necessarily holds a_i, so a state is just "what
 * the other CPU last ran".  Running a_{i+1} on the a_i CPU adds the same cost
 * to every state (a global offset), while running it on the other CPU moves
 * every state to "other = a_i", costing the best of cold from any state or hot
 * from state a_{i+1}.  Tracking the array minimum makes each step O(1).
 */

// #include <stdio.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P073_1799D2_hot_start_up.rocq.spec_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> list Z -> Z -> Prop)
*/

#define MAXK 300005
#define INF 0x3f3f3f3f3f3f3f3fLL

/* solver: minimum total running time.  d[] is scratch of size k+1 (state 0 is
 * the idle CPU). */
static long long solver(const int *a, int n, int k, const long long *cold,
                        const long long *hot, long long *d)
/*@ With (prog : list Z) (cold_costs : list Z) (hot_costs : list Z)
    Require
      1 <= n && n <= 300000 && 1 <= k && k <= 300000 && (forall i, (0 <= i && i < n) => (1 <= prog[i] && prog[i] <= k)) && (forall i, (0 <= i && i < k) => (1 <= hot_costs[i] && hot_costs[i] <= cold_costs[i] && cold_costs[i] <= 1000000000)) &&
      n == Zlength(prog) && k == Zlength(cold_costs) && Zlength(hot_costs) == k &&
      IntArray::full(a, n, prog) * Int64Array::full(cold, k + 1, cons(0, cold_costs)) * Int64Array::full(hot, k + 1, cons(0, hot_costs)) * Int64Array::undef_full(d, k + 1)
    Ensure
      Spec(prog, cold_costs, hot_costs, __return) &&
        IntArray::full(a, n, prog) * Int64Array::full(cold, k + 1, cons(0, cold_costs)) * Int64Array::full(hot, k + 1, cons(0, hot_costs)) * Int64Array::full_shape(d, k + 1)
*/
{
    for (int j = 0; j <= k; j++)
        d[j] = INF;
    d[0] = 0;                             /* second CPU still idle */
    long long off = cold[a[0]], mind = 0;
    for (int i = 1; i < n; i++) {
        int x = a[i], y = a[i - 1];
        long long costA = (x == y) ? hot[x] : cold[x];
        long long candB = mind + off + cold[x];
        if (d[x] < INF) {
            long long viaHot = d[x] + off + hot[x];
            if (viaHot < candB)
                candB = viaHot;
        }
        off += costA;                     /* run x on the CPU that held y */
        long long ny = candB - off;       /* run x on the other CPU instead */
        if (ny < d[y]) {
            d[y] = ny;
            if (ny < mind)
                mind = ny;
        }
    }
    return mind + off;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[MAXK];
//     static long long cold[MAXK], hot[MAXK], d[MAXK];
//     while (t--) {
//         int n, k;
//         scanf("%d %d", &n, &k);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         cold[0] = hot[0] = 0;
//         for (int j = 1; j <= k; j++)
//             scanf("%lld", &cold[j]);
//         for (int j = 1; j <= k; j++)
//             scanf("%lld", &hot[j]);
//         printf("%lld\n", solver(a, n, k, cold, hot, d));
//     }
//     return 0;
// }
