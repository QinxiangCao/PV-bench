/*@ Import Lean
import Codeforces.examples_shard00.P006_38A_army.lean.spec_lib
open scoped SimpleC
*/

/* Codeforces 38/A - Army */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
static int solver(const int *d, int a, int b)

/*@ With (years : list Z)
    Require
      2 <= Zlength(years) + 1 && Zlength(years) + 1 <= 100 &&
      (forall idx, (0 <= idx && idx < Zlength(years)) =>
        (1 <= years[idx] && years[idx] <= 100)) &&
      1 <= a && a < b && b <= Zlength(years) + 1 &&
      IntArray::full(d, Zlength(years) + 1, cons(0, years)) *
      IntArray::undef_seg(d, Zlength(years) + 1, 101)
    Ensure
      Spec(Zlength(years) + 1, years, a, b, __return) &&
      IntArray::full(d, Zlength(years) + 1, cons(0, years)) *
      IntArray::undef_seg(d, Zlength(years) + 1, 101)
*/

{
    int ans = 0;

    for (int i = a; i < b; ++i) ans += d[i];
    return ans;
}

// int main(void)
// {
//     int n, d[101] = {0}, a, b;
//     if (scanf("%d", &n) != 1) return 0;
//     for (int i = 1; i < n; ++i) scanf("%d", &d[i]);
//     scanf("%d %d", &a, &b);
//     printf("%d\n", solver(d, a, b));
//     return 0;
// }
