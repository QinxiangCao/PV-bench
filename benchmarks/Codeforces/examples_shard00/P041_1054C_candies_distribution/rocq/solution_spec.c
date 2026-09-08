/* Codeforces 1054/C - Candies Distribution */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : list Z -> list Z -> option (list Z) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P041_1054C_candies_distribution.rocq.spec_lib */

/*@ Extern Coq
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
static int solver(int n, const int *l, const int *r, int *a)

/*@ With (l_data : list Z)
             (r_data : list Z)
    Require
      1 <= Zlength(l_data) && Zlength(l_data) <= 1000 &&
      Zlength(r_data) == Zlength(l_data) &&
      (forall i, (0 <= i && i < Zlength(l_data)) => (0 <= l_data[i] && l_data[i] <= Zlength(l_data))) &&
      (forall i, (0 <= i && i < Zlength(r_data)) => (0 <= r_data[i] && r_data[i] <= Zlength(l_data))) &&
      n == Zlength(l_data) &&
      IntArray::full(l, n, l_data) * IntArray::full(r, n, r_data) *
      IntArray::undef_full(a, n)
    Ensure
      IntArray::full(l, n, l_data) * IntArray::full(r, n, r_data) *
      (((__return == 0 && Spec(l_data, r_data, None)) &&
        exists post, IntArray::full(a, n, post)) ||
       (exists result,
          __return == 1 && Spec(l_data, r_data, Some(result)) &&
          IntArray::full(a, n, result)))
*/

{
    
    for (int i = 0; i < n; ++i) a[i] = n - l[i] - r[i];
    
    for (int i = 0; i < n; ++i) {
        int cl = 0, cr = 0;
        
        for (int j = 0; j < i; ++j) cl += a[j] > a[i];
        
        for (int j = i + 1; j < n; ++j) cr += a[j] > a[i];
        if (a[i] < 1 || cl != l[i] || cr != r[i]) return 0;
    }
    return 1;
}

// int main(void)
// {
//     int n, l[1000], r[1000], a[1000];
//     if (scanf("%d", &n) != 1) return 0;
//     for (int i = 0; i < n; ++i) scanf("%d", &l[i]);
//     for (int i = 0; i < n; ++i) scanf("%d", &r[i]);
//     if (!solver(n, l, r, a)) { puts("NO"); return 0; }
//     puts("YES");
//     for (int i = 0; i < n; ++i) printf("%d%c", a[i], i + 1 == n ? '\n' : ' ');
//     return 0;
// }
