/* Codeforces 1747/A - Two Groups */
// #include <stdio.h>
// #include <stdlib.h>

/*@ Extern Coq
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
      (Z::abs : Z -> Z)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P002_1747A_two_groups.rocq.spec_lib */

static long long llabs(long long x)

{
    return x < 0 ? -x : x;
}

static long long solver(const long long *a, int n)

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (-1000000000 <= input[i] && input[i] <= 1000000000)) &&
      Int64Array::full(a, n, input) *
      Int64Array::undef_seg(a, n, 100005)
    Ensure
      Spec(input, __return) &&
      Int64Array::full(a, n, input) *
      Int64Array::undef_seg(a, n, 100005)
*/

{
    long long sum = 0;
    
    for (int i = 0; i < n; ++i) sum += a[i];
    return llabs(sum);
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1) return 0;
//     while (t--) {
//         int n; long long a[100005];
//         scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//         printf("%lld\n", solver(a, n));
//     }
//     return 0;
// }
