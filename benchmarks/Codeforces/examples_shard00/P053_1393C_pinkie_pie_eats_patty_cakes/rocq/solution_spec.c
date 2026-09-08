/* Codeforces 1393/C - Pinkie Pie Eats Patty-cakes */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes.rocq.spec_lib */

void *calloc(unsigned long nmemb, unsigned long size)
/*@ calloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, cap, repeat_Z(0, cap))
*/;

void free(void *ptr)
/*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/;

static int solver(const int *a, int n) 

/*@ With (values : list Z)
    Require
      2 <= Zlength(values) && Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= Zlength(values))) &&
      Pre(values) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) && IntArray::full(a, n, values)
*/

{
    int *cnt = calloc((size_t)n + 1, sizeof(*cnt))
      ;

    int mx = 0;
    int c = 0;

    for (int i = 0; i < n; ++i) {
        ++cnt[a[i]];
    }

    for (int i = 1; i <= n; ++i) {
        if (cnt[i] > mx) {
            mx = cnt[i];
            c = 1;
        } else if (cnt[i] == mx) {
            ++c;
        }
    }

    int ans = (n - c) / (mx - 1) - 1;

    free(cnt) ;
    return ans;
}

// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//
//         int *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i) {
//             scanf("%d", &a[i]);
//         }
//
//         printf("%d\n", solver(a, n));
//         free(a);
//     }
//
//     return 0;
// }
