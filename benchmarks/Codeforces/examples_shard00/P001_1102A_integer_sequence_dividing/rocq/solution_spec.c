/* Codeforces 1102/A - Integer Sequence Dividing */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
*/

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
