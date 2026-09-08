/* Codeforces 1903/C - Theofanis' Nightmare */
// #include <stdio.h>
// #include <stdlib.h>

/*@ Extern Coq
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P038_1903C_theofanis_nightmare.rocq.spec_lib */

static long long solver(const long long *a, int n)

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (-100000000 <= input[i] && input[i] <= 100000000)) &&
      Int64Array::full(a, n, input)
    Ensure
      Spec(input, __return) &&
      Int64Array::full(a, n, input)
*/

{
    long long suffix = 0, answer = 0;
    
    for (int i = n - 1; i >= 0; --i) {
        suffix += a[i];
        if (i == 0 || suffix > 0) answer += suffix;
    }
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); long long *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//         printf("%lld\n", solver(a, n)); free(a);
//     }
//     return 0;
// }
