/* Codeforces 567/C - Geometric Progression */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P055_567C_geometric_progression.rocq.spec_lib */

void *malloc(size_t size)
/*@ malloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      size == cap * sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::undef_full(__return, cap)
*/;

void *calloc(size_t nmemb, size_t size)
/*@ calloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, cap, repeat_Z(0, cap))
*/;

void qsort(long long *base, size_t nmemb, size_t size,
           int (*compar)(const void *, const void *))
/*@ qsort_int64
    With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      size == sizeof(long long) &&
      Int64Array::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        increasing(sorted) &&
        Zlength(sorted) == nmemb &&
        Int64Array::full(base, nmemb, sorted)
*/;

void free(void *ptr)
/*@ free_int64
    Require exists values cap,
      Int64Array::full(ptr, cap, values)
    Ensure emp
*/;

static int cmp_ll(const void *x, const void *y)

{
    long long a = *(const long long *)x;
    long long b = *(const long long *)y;
    return (a > b) - (a < b);
}

static int lower_bound_ll(const long long *a, int n, long long x)

{
    int l = 0;
    int r = n;
    
    while (l < r) {
        int m = (l + r) / 2;
        
        if (a[m] < x) {
            l = m + 1;
        } else {
            r = m;
        }
    }
    return l;
}

static long long solver(const long long *input, int n, long long k)

/*@ With (values : list Z)
    Require
      1 <= k && k <= 200000 &&
      1 <= Zlength(values) && Zlength(values) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(values)) =>
        (-1000000000 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) &&
      Int64Array::full(input, n, values)
    Ensure
      Spec(k, values, __return) &&
      Int64Array::full(input, n, values)
*/

{
    long long *a = malloc((size_t)n * sizeof(*a))
      ;
    long long *vals = malloc((size_t)n * sizeof(*vals))
      ;

    for (int i = 0; i < n; ++i) {
        a[i] = input[i];
        vals[i] = input[i];
    }

    qsort(vals, (size_t)n, sizeof(*vals), cmp_ll)
      ;

    int un = 0;
    
    for (int i = 0; i < n; ++i) {
        if (i == 0 || vals[i] != vals[i - 1]) {
            vals[un] = vals[i];
            ++un;
        }
    }

    long long *left = calloc((size_t)un, sizeof(*left))
      ;
    long long *right = calloc((size_t)un, sizeof(*right))
      ;

    for (int i = 0; i < n; ++i) {
        int index = lower_bound_ll(vals, un, a[i]);
        
        ++right[index];
    }

    long long ans = 0;
    
    for (int i = 0; i < n; ++i) {
        int ix = lower_bound_ll(vals, un, a[i]);
        
        --right[ix];
        if (a[i] % k == 0) {
            long long lo = a[i] / k;
            long long hi = a[i] * k;
            int li = lower_bound_ll(vals, un, lo);
            int ri = lower_bound_ll(vals, un, hi);
            if (li < un && vals[li] == lo &&
                ri < un && vals[ri] == hi) {
                ans += left[li] * right[ri];
            }
        }
        ++left[ix];
    }

    free(a) ;
    free(vals) ;
    free(left) ;
    free(right) ;
    return ans;
}

// int main(void)
// {
//     int n;
//     long long k;
//     if (scanf("%d %lld", &n, &k) != 2) return 0;
//     long long *a = malloc((size_t)n * sizeof(*a));
//     for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//     printf("%lld\n", solver(a, n, k));
//     free(a);
//     return 0;
// }
