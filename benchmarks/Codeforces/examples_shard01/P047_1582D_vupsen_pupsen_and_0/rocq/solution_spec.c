/*
 * Codeforces 1582/D - Vupsen, Pupsen and 0  (rating 1600, CONSTRUCTIVE)
 *
 * Pair the entries up: (a, b) is cancelled by (b/g, -a/g) with g = gcd, which
 * is non-zero and keeps the values small.  An odd length leaves a leading
 * triple: pick two of its three entries whose sum is non-zero, say a1 + a2,
 * and answer (a3, a3, -(a1+a2)) — always non-zero and summing to 0.
 */

// #include <stdio.h>
// #include <stdlib.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P047_1582D_vupsen_pupsen_and_0.rocq.spec_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Prop)
*/


static long long llabs(long long x)
{
    return x < 0 ? -x : x;
}


static long long gcdll(long long a, long long b)
{
    while (b) {
        long long r = a % b;
        a = b;
        b = r;
    }
    return a < 0 ? -a : a;
}

/* pair_fill: cancels the pair (a, b) into b_out[0], b_out[1]. */
static void pair_fill(long long a, long long b, long long *out)
{
    long long g = gcdll(llabs(a), llabs(b));
    out[0] = b / g;
    out[1] = -a / g;
}

/* solver: pure.  Fills b[0..n-1] with a non-zero array orthogonal to a[]. */
static void solver(const int *a, int n, long long *b)
/*@ With (values : list Z)
    Require
      2 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (-10000 <= values[i] && values[i] <= 10000 && values[i] != 0)) &&
      n == Zlength(values) && IntArray::full(a, n, values) * Int64Array::undef_full(b, n)
    Ensure
      exists (out : list Z),
        Spec(values, out) &&
        IntArray::full(a, n, values) * Int64Array::full(b, n, out)
*/
{
    int start = 0;
    if (n % 2) {                           /* consume a leading triple */
        long long x = a[0], y = a[1], z = a[2];
        if (x + y != 0) {
            b[0] = z; b[1] = z; b[2] = -(x + y);
        } else if (x + z != 0) {
            b[0] = y;
            b[2] = y;
            b[1] = -(x + z);
        } else {
            b[1] = x; b[2] = x; b[0] = -(y + z);
        }
        start = 3;
    }
    for (int i = start; i + 1 < n; i += 2) {
        pair_fill(a[i], a[i + 1], b + i);
    }
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[100005];
//     static long long b[100005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         solver(a, n, b);
//         for (int i = 0; i < n; i++)
//             printf("%lld%c", b[i], i + 1 == n ? '\n' : ' ');
//     }
//     return 0;
// }
