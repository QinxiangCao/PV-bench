/* Codeforces 435/A - Queue on Bus Stop */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P015_435A_queue_on_bus_stop.rocq.spec_lib */

static int solver(const int *groups, int n,
                  int capacity) 

/*@ With (groups_data : list Z)
    Require
      1 <= Zlength(groups_data) && Zlength(groups_data) <= 100 &&
      1 <= capacity && capacity <= 100 &&
      (forall i, (0 <= i && i < Zlength(groups_data)) => (1 <= groups_data[i] && groups_data[i] <= capacity)) &&
      n == Zlength(groups_data) &&
      IntArray::full(groups, n, groups_data)
    Ensure
      Spec(capacity, groups_data, __return) &&
      IntArray::full(groups, n, groups_data)
*/

{
    int buses = 1, used = 0;
    
    for (int i = 0; i < n; ++i)
    {
        if (used + groups[i] > capacity)
        {
            ++buses;
            used = 0;
        }
        used += groups[i];
    }
    return buses;
}

// int main(void)
// {
//     int n, m, groups[100];
//     if (scanf("%d %d", &n, &m) != 2) return 0;
//     for (int i = 0; i < n; ++i) scanf("%d", &groups[i]);
//     printf("%d\n", solver(groups, n, m));
//     return 0;
// }
