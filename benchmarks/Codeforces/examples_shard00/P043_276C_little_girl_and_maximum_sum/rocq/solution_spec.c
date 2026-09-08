/* Codeforces 276/C - Little Girl and Maximum Sum */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

static int cmp_ll(const void *x, const void *y)
{
    long long a = *(const long long *)x, b = *(const long long *)y;
    return (a > b) - (a < b);
}

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : list Z -> list (Z*Z) -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P043_276C_little_girl_and_maximum_sum.rocq.spec_lib */

/*@ Extern Coq
      (increasing : list Z -> Prop)
*/

void *calloc(unsigned long nmemb, unsigned long size)
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

void qsort(long long *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
/*@ With (contents : list Z)
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

static long long solver(long long *a, int n, const int *left, const int *right, int q)

/*@ With (values : list Z)
             (queries : list (Z*Z))
             (lefts rights : list Z)
    Require
      1 <= Zlength(values) && Zlength(values) <= 200000 &&
      1 <= Zlength(queries) && Zlength(queries) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 200000)) &&
      (forall i, (0 <= i && i < Zlength(queries)) => ((0 <= fst(queries[i]) && fst(queries[i]) <= snd(queries[i])) && (snd(queries[i]) < Zlength(values)))) &&
      n == Zlength(values) &&
      q == Zlength(queries) &&
      Zlength(lefts) == q && Zlength(rights) == q &&
      (forall i, (0 <= i && i < q) =>
        (fst(queries[i]) == lefts[i] - 1 &&
         snd(queries[i]) == rights[i] - 1)) &&
      Int64Array::full(a, n, values) *
      IntArray::full(left, q, lefts) *
      IntArray::full(right, q, rights)
    Ensure
      exists values_after,
        Spec(values, queries, __return) &&
        Permutation(values, values_after) &&
        Int64Array::full(a, n, values_after) *
        IntArray::full(left, q, lefts) *
        IntArray::full(right, q, rights)
*/

{
    long long *diff = calloc((size_t)n + 1, sizeof(*diff))
      ;
    
    for (int i = 0; i < q; ++i) {
        
        ++diff[left[i] - 1];
        --diff[right[i]];
    }
    
    for (int i = 1; i < n; ++i)
        diff[i] += diff[i - 1];
    
    qsort(a, (size_t)n, sizeof(*a), cmp_ll);
    
    qsort(diff, (size_t)n, sizeof(*diff), cmp_ll);
    
    long long answer = 0;
    
    for (int i = 0; i < n; ++i)
        answer += a[i] * diff[i];
    free(diff) ;
    return answer;
}

// int main(void)
// {
//     int n, q; if (scanf("%d %d", &n, &q) != 2) return 0;
//     long long *a = malloc((size_t)n * sizeof(*a));
//     int *left = malloc((size_t)q * sizeof(*left)), *right = malloc((size_t)q * sizeof(*right));
//     for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//     for (int i = 0; i < q; ++i) scanf("%d %d", &left[i], &right[i]);
//     printf("%lld\n", solver(a, n, left, right, q)); free(a); free(left); free(right);
//     return 0;
// }
