/* Codeforces 630/I - Parking Lot */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
      (Z::pow : Z -> Z -> Z)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P056_630I_parking_lot.rocq.spec_lib */

static long long power4(int e)
/*@
    Require
      -1 <= e && e <= 27
    Ensure
      (0 <= e && __return == Z::pow(4, e)) ||
      (e == -1 && __return == 1)
*/
{
    long long r = 1;

    /*@ Inv Assert
          ((e@pre == -1 && e == -1 && r == 1) ||
           (0 <= e && e <= e@pre && e@pre <= 27 &&
            r == Z::pow(4, e@pre - e) &&
            1 <= r && r <= 18014398509481984 &&
            (0 < e => r <= 4503599627370496)))
    */
    while (e > 0)
    {
        r *= 4;
        e -= 1;
    }

    return r;
}

static long long solver(int n)

/*@
    Require
      3 <= n && n <= 30
    Ensure
      Spec(n, __return)
*/

{
    long long first = power4(n - 3);
    long long second = power4(n - 4);

    return 24 * first + (long long)(n - 3) * 36 * second;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     printf("%lld\n", solver(n));
//     return 0;
// }
