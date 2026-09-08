/*
 * Codeforces 1787/B - Number Factorization  (rating 1100, NUMBER THEORY)
 *
 * Each a_i must be squarefree, so writing n = prod q_j^{e_j} the factors split
 * into "layers": layer k (for k = 1 .. max e_j) may use every prime whose
 * exponent is at least k.  Multiplying a whole layer into one a_i with p_i = 1
 * beats splitting it, since for primes u,v the product u*v >= u + v when
 * u,v >= 2.  So the answer is the sum over layers of the layer's product.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P019_1787B_number_factorization.rocq.spec_lib */

/* solver: pure.  Maximum of sum a_i * p_i over valid factorisations of n. */
static long long solver(long long n)
/*@
    Require
      2 <= n && n <= 1000000000 &&
      emp
    Ensure
      Spec(n@pre, __return) &&
      emp
*/
{
    long long pr[40], ex[40];
    int m = 0;
    for (long long d = 2; d * d <= n; d++)
        if (n % d == 0) {
            pr[m] = d;
            ex[m] = 0;
            while (n % d == 0) {
                n /= d;
                ex[m]++;
            }
            m++;
        }
    if (n > 1) {
        pr[m] = n;
        ex[m] = 1;
        m++;
    }
    long long maxe = 0;
    for (int i = 0; i < m; i++)
        if (ex[i] > maxe)
            maxe = ex[i];
    long long total = 0;
    for (long long k = 1; k <= maxe; k++) {
        long long prod = 1;
        for (int i = 0; i < m; i++)
            if (ex[i] >= k)
                prod *= pr[i];
        total += prod;
    }
    return total;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         long long n;
//         scanf("%lld", &n);
//         printf("%lld\n", solver(n));
//     }
//     return 0;
// }
