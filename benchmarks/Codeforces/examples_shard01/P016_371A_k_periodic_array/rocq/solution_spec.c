/*
 * Codeforces 371/A - K-Periodic Array  (rating 1000, GREEDY)
 *
 * Positions sharing a residue mod k must all end up equal, and they are
 * independent across residues.  For each residue keep the majority value and
 * change the rest, i.e. add min(#ones, #twos).
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P016_371A_k_periodic_array.rocq.spec_lib */

/* solver: pure.  Minimum changes to make a[0..n-1] (values 1/2) k-periodic. */
static int solver(const int *a, int n, int k)
/*@ With (values : list Z)
    Require
      Pre(k, values) && 1 <= k && k <= n && n <= 100 &&
      (forall i, (0 <= i && i < n) => (values[i] == 1 || values[i] == 2)) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(k, values, __return) &&
      IntArray::full(a, n, values)
*/
{
    int changes = 0;
    for (int r = 0; r < k; r++) {
        int ones = 0, twos = 0;
        for (int i = r; i < n; i += k) {
            if (a[i] == 1)
                ones++;
            else
                twos++;
        }
        changes += ones < twos ? ones : twos;
    }
    return changes;
}

// int main(void)
// {
//     int n, k;
//     if (scanf("%d %d", &n, &k) != 2)
//         return 0;
//     static int a[105];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%d\n", solver(a, n, k));
//     return 0;
// }
