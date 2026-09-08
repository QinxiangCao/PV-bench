/* Codeforces 1454/D - Number into Sequence */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> list Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P033_1454D_number_into_sequence.rocq.spec_lib */
/*@ Extern Coq
      (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
*/

static int solver(long long n,
                  long long *out) 

/*@
    Require
      2 <= n && n <= 10000000000 &&
      Int64Array::undef_full(out, 64)
    Ensure
      exists result,
        Spec(n, result) && __return == Zlength(result) &&
        Int64Array::full(out, __return, result) *
        Int64Array::undef_seg(out, __return, 64)
*/

{
    long long value = n, best_prime = n;
    int best_exp = 1;
    
    for (long long p = 2; p * p <= value; ++p)
        if (value % p == 0)
        {
            int e = 0;
            
            while (value % p == 0)
            {
                value /= p;
                ++e;
            }
            
            if (e > best_exp)
            {
                best_exp = e;
                best_prime = p;
            }
        }
    
    long long rest = n;
    
    for (int i = 0; i + 1 < best_exp; ++i)
    {
        out[i] = best_prime;
        rest /= best_prime;
    }
    
    out[best_exp - 1] = rest;
    
    return best_exp;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         long long n, out[64]; scanf("%lld", &n);
//         int count = solver(n, out); printf("%d\n", count);
//         for (int i = 0; i < count; ++i) printf("%lld%c", out[i], i + 1 == count ? '\n' : ' ');
//     }
//     return 0;
// }
