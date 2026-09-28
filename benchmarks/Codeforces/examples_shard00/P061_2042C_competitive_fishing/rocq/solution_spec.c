/* Codeforces 2042/C - Competitive Fishing */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;
static int cmp_desc(const void *x, const void *y)

{
    int a = *(const int *)x, b = *(const int *)y;
    return (b > a) - (b < a);
}
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Permutation : list Z -> list Z -> Prop)
      (decreasing : list Z -> Prop)
      (GainBuildState : list Z -> Z -> list Z -> Z -> Prop)
      (PreparedGains : list Z -> list Z -> Prop)
      (GainSearchState : Z -> list Z -> Z -> Z -> Prop)
      (FishingSearchResult : Z -> list Z -> list Z -> Z -> Prop)
*/

void *malloc(unsigned long size)
/*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap && size == cap * sizeof(int)
    Ensure
      __return != 0 && IntArray::undef_full(__return, cap)
*/;

void qsort(int *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
;

void free(void *ptr)
/*@ free_int
    With (values : list Z)
    Require
      IntArray::full(ptr, Zlength(values), values)
    Ensure emp
*/;

static int solver(const char *s, int n,
                  long long k) 
/*@ With (f : list Z)
    Require
      2 <= Zlength(f) && Zlength(f) <= 200000 &&
      1 <= k && k <= 1000000000 &&
      (forall i, (0 <= i && i < Zlength(f)) =>
        (f[i] == 48 || f[i] == 49)) &&
      n == Zlength(f) &&
      CharArray::full(s, n + 1, app(f, cons(0, nil)))
    Ensure
      Spec(k, f, __return) &&
      CharArray::full(s, n + 1, app(f, cons(0, nil)))
*/
{
    int *gain = malloc((size_t)(n - 1) * sizeof(*gain))
        ,
        sum = s[n - 1] == '1' ? 1 : -1;
    
    for (int i = n - 2; i >= 0; --i)
    {
        gain[i] = sum;
        sum += s[i] == '1' ? 1 : -1;
    }
    
    qsort(gain, (size_t)(n - 1), sizeof(*gain), cmp_desc);
    
    long long cur = 0;
    int ans = -1;
    
    for (int i = 0; i < n - 1; ++i)
    {
        cur += gain[i];
        if (cur >= k)
        {
            ans = i + 2;
            break;
        }
    }

    free(gain) ;
    return ans;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n;
//         long long k;
//         char *s;
//         scanf("%d %lld", &n, &k);
//         s = malloc((size_t)n + 1);
//         scanf("%s", s);
//         printf("%d\n", solver(s, n, k));
//         free(s);
//     }
//     return 0;
// }
