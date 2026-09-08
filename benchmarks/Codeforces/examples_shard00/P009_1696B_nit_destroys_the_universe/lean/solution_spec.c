/*@ Import Lean
import Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe.lean.spec_lib
open scoped SimpleC
*/

/* Codeforces 1696/B - NIT Destroys the Universe */
// #include <stdio.h>

/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/

static int solver(const int *a,
                  int n)

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (0 <= input[i] && input[i] <= 1000000000)) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 200005)
    Ensure
      Spec(input, __return) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 200005)
*/

{
    int runs = 0, inside = 0;

    for (int i = 0; i < n; ++i)
    {
        if (a[i] != 0 && !inside)
        {
            ++runs;
            inside = 1;
        }
        if (a[i] == 0)
            inside = 0;
    }
    return runs > 2 ? 2 : runs;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, a[200005]; scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n));
//     }
//     return 0;
// }
