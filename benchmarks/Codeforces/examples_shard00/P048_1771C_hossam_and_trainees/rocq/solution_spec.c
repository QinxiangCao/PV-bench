/* Codeforces 1771/C - Hossam and Trainees */
// #include <stdio.h>
// #include <stdlib.h>

static int cmp_int(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}

/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees.rocq.spec_lib */

/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::full_shape : Z -> Z -> Assertion)
      (UCharArray::full : Z -> Z -> list Z -> Assertion)
      (UCharArray::undef_full : Z -> Z -> Assertion)
*/

void *malloc(unsigned int size)
    /*@ malloc_int
  With (cap : Z)
  Require
    0 <= cap &&
    cap * sizeof(int) <= 4294967295 &&
    size == cap * sizeof(int)
  Ensure
    __return != 0 &&
    IntArray::undef_full(__return, cap)
*/
    ;

void qsort(int *base, unsigned int nmemb, unsigned int size,
           int (*compar)(const void *, const void *))
    /*@ With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      size == sizeof(int) &&
      IntArray::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        increasing(sorted) &&
        Zlength(sorted) == nmemb &&
        IntArray::full(base, nmemb, sorted)
*/
    ;

void free(void *ptr)
    /*@ free_int
  With (len : Z) (cap : Z)
  Require
    0 <= len && len <= cap &&
    exists xs,
      Zlength(xs) == len &&
      IntArray::full(ptr, len, xs) *
      IntArray::undef_seg(ptr, len, cap)
  Ensure emp
*/
    ;

static int solver(const int *values,
                  int n) 

/*@ With (a : list Z)
    Require
      2 <= Zlength(a) && Zlength(a) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(a)) => (1 <= a[i] && a[i] <= 1000000000)) &&
      n == Zlength(a) && IntArray::full(values, n, a)
    Ensure
      Spec(a, __return) &&
      IntArray::full(values, n, a)
*/

{
    int primes[4000];
    int pc = 0;
    unsigned char composite[31624] = {0};
    
    for (int i = 2; i <= 31623; ++i)
        if (!composite[i])
        {
            primes[pc] = i;
            pc++;
            if ((long long)i * i <= 31623)
                
                for (int j = i * i; j <= 31623; j += i)
                    composite[j] = 1;
        }
    int *factors = malloc(n * 10 * sizeof(*factors))
        ;
    int count = 0;
    
    for (int i = 0; i < n; ++i)
    {
        int x = values[i];
        
        for (int j = 0; j < pc && (long long)primes[j] * primes[j] <= x; ++j)
            if (x % primes[j] == 0)
            {
                factors[count] = primes[j];
                count++;
                
                while (x % primes[j] == 0)
                    x /= primes[j];
            }
        if (x > 1)
        {
            factors[count] = x;
            count++;
        }
    }
    qsort(factors, count, sizeof(*factors), cmp_int);
    int ok = 0;
    
    for (int i = 1; i < count; ++i)
        if (factors[i] == factors[i - 1])
            ok = 1;
    
    free(factors) ;
    
    return ok;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); int *values = malloc((size_t)n * sizeof(*values));
//         for (int i = 0; i < n; ++i) scanf("%d", &values[i]);
//         puts(solver(values, n) ? "YES" : "NO"); free(values);
//     }
//     return 0;
// }
