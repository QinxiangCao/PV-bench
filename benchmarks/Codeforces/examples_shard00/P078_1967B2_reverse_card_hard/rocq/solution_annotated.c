/* Codeforces 1967/B2 - Reverse Card (Hard Version) */
// #include <stdio.h>
/*@ Extern Coq (RCgcd : Z -> Z -> Z)
               (RCProgress : Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P078_1967B2_reverse_card_hard.rocq.helper_lib */
static int gcd_int(int a, int b)
/*@ Require 1 <= a && a <= 2000000 && 1 <= b && b <= 2000000
    Ensure __return == RCgcd(a, b)
*/
{
    /*@ Inv Assert
        0 <= a && a <= 2000000 && 0 <= b && b <= 2000000 &&
        RCgcd(a, b) == RCgcd(a@pre, b@pre)
    */
    while (b)
    {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P078_1967B2_reverse_card_hard.rocq.helper_lib */
static long long solver(int n, int m) 
/*@
    Require
      1 <= n && n <= 2000000 &&
      1 <= m && m <= 2000000
    Ensure
      Spec(n, m, __return)
*/
{
    long long ans = 0;
    /*@ Inv Assert
        n == n@pre && m == m@pre &&
        1 <= n && n <= 2000000 && 1 <= m && m <= 2000000 &&
        1 <= p && p <= 1415 &&
        0 <= ans && ans <= 2000000 * ((p - 1) * 1415) &&
        RCProgress(n, m, p, 1, ans)
    */
    for (int p = 1; (long long)p * p < n; ++p)
        /*@ Inv Assert
            n == n@pre && m == m@pre &&
            1 <= n && n <= 2000000 && 1 <= m && m <= 2000000 &&
            1 <= p && p <= 1415 && p * p < n &&
            1 <= q && q <= 1415 &&
            0 <= ans && ans <= 2000000 * ((p - 1) * 1415 + (q - 1)) &&
            RCProgress(n, m, p, q, ans)
        */
        for (int q = 1; (long long)q * q < m; ++q)
            if (gcd_int(p, q) == 1)
            {
                int lim = n / p < m / q ? n / p : m / q;
                ans += lim / (p + q);
            }
    return ans;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n, m;
//         scanf("%d %d", &n, &m);
//         printf("%lld\n", solver(n, m));
//     }
//     return 0;
// }
