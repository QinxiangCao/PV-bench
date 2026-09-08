/*@ Import Lean
import Codeforces.examples_shard00.P026_1355A_sequence_with_digits.lean.spec_lib
open scoped SimpleC
*/

/* Codeforces 1355/A - Sequence with Digits */
// #include <stdio.h>

static long long step(long long x)

{
    int mn = 9, mx = 0;

    while (x)
    {
        int d = (int)(x % 10);
        x /= 10;
        if (d < mn)
            mn = d;
        if (d > mx)
            mx = d;
    }
    return (long long)mn * mx;
}

/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
static long long solver(long long a,
                        long long k)

/*@ With (a1 : Z)
    Require
      1 <= a1 && a1 <= 1000000000000000000 &&
      1 <= k && k <= 10000000000000000 &&
      a == a1
    Ensure
      Spec(a1, k, __return)
*/

{

    for (long long i = 1; i < k; ++i)
    {
        long long add = step(a);
        if (!add)

            break;
        a += add;
    }
    return a;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         long long a, k; scanf("%lld %lld", &a, &k);
//         printf("%lld\n", solver(a, k));
//     }
//     return 0;
// }
