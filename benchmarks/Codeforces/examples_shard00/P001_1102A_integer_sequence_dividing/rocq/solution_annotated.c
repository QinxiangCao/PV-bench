/* Codeforces 1102/A - Integer Sequence Dividing */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P001_1102A_integer_sequence_dividing.rocq.spec_lib */
static long long solver(long long n)
/*@ Require
      1 <= n && n <= 2000000000
    Ensure
      Spec(n, __return)
*/

{
    return (n * (n + 1) / 2) & 1LL;
}

// int main(void)
// {
//     long long n;
//     if (scanf("%lld", &n) == 1) printf("%lld\n", solver(n));
//     return 0;
// }
