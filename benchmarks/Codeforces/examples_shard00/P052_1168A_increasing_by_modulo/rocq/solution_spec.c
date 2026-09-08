/* Codeforces 1168/A - Increasing by Modulo */
// #include <stdio.h>
// #include <stdlib.h>

static int n, m, *a;

/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P052_1168A_increasing_by_modulo.rocq.spec_lib */

static int feasible(int x)

{
    int last = 0;

    for (int i = 0; i < n; ++i) {
        if (a[i] + x < m) {
            if (a[i] + x < last) {
                return 0;
            }
            if (a[i] > last) {
                last = a[i];
            }
        } else {
            int wrapped = (a[i] + x) % m;

            if (a[i] > last && wrapped < last) {
                last = a[i];
            }
        }
    }

    return 1;
}

static int solver(int nn, int mm, const int *input) 

/*@ With (modulus : Z)
             (values : list Z)
             (n_before m_before a_before : Z)
    Require
      1 <= modulus && modulus <= 300000 &&
      1 <= Zlength(values) && Zlength(values) <= 300000 &&
      (forall i, (0 <= i && i < Zlength(values)) =>
        (0 <= values[i] && values[i] < modulus)) &&
      nn == Zlength(values) && mm == modulus &&
      IntArray::full(input, nn, values) *
      store(&n, int, n_before) *
      store(&m, int, m_before) *
      store(&a, int *, a_before)
    Ensure
      Spec(modulus, values, __return) &&
      IntArray::full(input, nn, values) *
      store(&n, int, nn) *
      store(&m, int, mm) *
      store(&a, int *, 0)
*/

{
    n = nn;
    m = mm;
    a = (int *)input;

    int lo = 0;
    int hi = m - 1;
    int ans = hi;

    while (lo <= hi) {
        int mid = (lo + hi) / 2;

        if (feasible(mid) ) {
            ans = mid;
            hi = mid - 1;
        } else {
            lo = mid + 1;
        }
    }

    a = 0;
    return ans;
}

// int main(void)
// {
//     if (scanf("%d %d", &n, &m) != 2) {
//         return 0;
//     }
//
//     a = malloc((size_t)n * sizeof(*a));
//     for (int i = 0; i < n; ++i) {
//         scanf("%d", &a[i]);
//     }
//
//     int *out = a;
//     printf("%d\n", solver(n, m, out));
//     free(out);
//     return 0;
// }
