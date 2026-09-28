/* Codeforces 1977/C - Nikita and LCM */
// #include <stdio.h>
// #include <stdlib.h>
/*@ Extern Coq
      (GcdValue : Z -> Z -> Z)
      (LcmCapValue : Z -> Z -> Z -> Z -> Prop)
      (CompareResult : Z -> Z -> Z -> Prop)
*/
static long long gcdll(long long a, long long b)

{
    
    while (b)
    {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static long long lcm_cap(long long a, long long b, long long cap)

{
    long long g = gcdll(a, b);
    
    if (a / g > cap / b)
        return cap + 1;
    long long x = a / g * b;
    return x > cap ? cap + 1 : x;
}
static int cmp_int(const void *x, const void *y)

{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/

/*@ Extern Coq
      (IntArray::undef_full : Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (GcdValue : Z -> Z -> Z)
      (LcmCapValue : Z -> Z -> Z -> Z -> Prop)
      (CompareResult : Z -> Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (CopyMaxState : list Z -> list Z -> Z -> Z -> Prop)
      (LcmPrefixState : list Z -> Z -> Z -> Z -> Prop)
      (DivisorBestState : list Z -> Z -> Z -> Z -> Z -> Prop)
      (DivisorScanState : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

void *malloc(unsigned long size)
/*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      size == cap * sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::undef_full(__return, cap)
*/;

void free(void *ptr)
/*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/;

void qsort(int *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
;

static int solver(int *input, int n) 
/*@ With (a : list Z)
    Require
      1 <= Zlength(a) && Zlength(a) <= 2000 &&
      (forall i, (0 <= i && i < Zlength(a)) => (1 <= a[i] && a[i] <= 1000000000)) &&
      n == Zlength(a) && IntArray::full(input, n, a)
    Ensure
      Spec(a, __return) && IntArray::full(input, n, a)
*/
{
    
    int *a = malloc(n * sizeof(*a))
        ;
    
    int mx = 0;
    long long all = 1;
    
    for (int i = 0; i < n; ++i)
    {
        a[i] = input[i];
        if (a[i] > mx)
            mx = a[i];
    }

    for (int i = 0; i < n; ++i)
        all = lcm_cap(all, a[i], mx);
    if (all != mx)
    {
        
        free(a);
        return n;
    }
    qsort(a, n, sizeof(*a), cmp_int);

    int ans = 0;
    
    for (int q = 1; (long long)q * q <= mx; ++q)
        if (mx % q == 0)
        {
            int ds[2] = {q, mx / q};
            
            for (int z = 0; z < 2; ++z)
            {
                int d = ds[z], present = 0, count = 0;
                long long l = 1;
                
                for (int i = 0; i < n; ++i)
                {
                    if (a[i] == d)
                        present = 1;
                    if (d % a[i] == 0)
                    {
                        ++count;
                        l = lcm_cap(l, a[i], d);
                    }
                }
                if (!present && l == d && count > ans)
                    ans = count;
            }
        }
    
    free(a);
    return ans;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n;
//         scanf("%d", &n);
//         int *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i)
//             scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n));
//         free(a);
//     }
//     return 0;
// }
