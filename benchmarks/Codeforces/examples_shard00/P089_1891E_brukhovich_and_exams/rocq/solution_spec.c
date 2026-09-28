// #include <stdio.h>
// #include <stdlib.h>
typedef long long i64;
typedef unsigned long size_t;
/*@ Extern Coq
      (GcdResult : Z -> Z -> Z -> Prop)
      (MinValue : Z -> Z -> Z -> Prop)
*/
static i64 gcdll(i64 a, i64 b)

{
    
    while (b)
    {
        i64 t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static int cmpi(const void *A, const void *B)

{
    return *(const int *)A - *(const int *)B;
}
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/

/*@ Extern Coq
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (AllOnePrefix : list Z -> Z -> Z -> Prop)
      (CoprimeEdgePrefixCount : list Z -> Z -> Z -> Prop)
      (PairSavingsPrefix : list Z -> Z -> Z -> Prop)
      (PairSavingsScan : list Z -> Z -> Z -> Z -> Z -> Prop)
      (PairRunSuffix : list Z -> Z -> Z -> Prop)
      (InteriorOneRunPrefix : list Z -> Z -> list Z -> Prop)
      (OneRunScanState : list Z -> Z -> Z -> list Z -> Prop)
      (GreedyBlockState : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OptimizationSafetyBounds : Z -> Z -> list Z -> Prop)
      (JointPairBlockPrefix : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (ExamCompetitorChargingPrefix : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (ExamBlockCollectionCertificate : list Z -> Z -> Z -> list Z -> Prop)
      (ExamJointOptimizationCertificate : list Z -> Z -> Z -> list Z -> Prop)
      (ExamPrefixLowerBound : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (ExamGreedyAttainability : list Z -> Z -> Z -> list Z -> Prop)
      (CanonicalInteriorOneRunPrefix : list Z -> Z -> list Z -> Prop)
      (CanonicalOneRunScanState : list Z -> Z -> Z -> list Z -> Prop)
      (CanonicalExamBlockCollectionCertificate : list Z -> Z -> Z -> list Z -> Prop)
      (FinalBudgetResult : Z -> Z -> Z -> Prop)
      (ExamOptimizationSummary : list Z -> Z -> Z -> list Z -> Prop)
*/

void *malloc(unsigned long size)
/*@ malloc_int
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/;

void qsort(int *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
;

void free(void *ptr)
/*@ free_int_prefix
    With (cap used : Z) (contents : list Z)
    Require
      0 <= used && used <= cap &&
      IntArray::seg(ptr, 0, used, contents) *
      IntArray::undef_seg(ptr, used, cap)
    Ensure emp
*/;
static int solver(int n, int k,
                  const i64 *a) 
/*@ With (values : list Z)
    Require
      1 <= k && k <= Zlength(values) &&
      Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (0 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) &&
      Int64Array::full(a, n, values)
    Ensure
      Spec(k, values, __return) &&
      Int64Array::full(a, n, values)
*/
{
    int allone = 1;
    
    for (int i = 0; i < n; i++)
        if (a[i] != 1)
            allone = 0;
    if (allone)
        return k == n ? 0 : n - k;
    int sad = 0, two = 0;
    
    for (int i = 0; i + 1 < n; i++)
        if (gcdll(a[i], a[i + 1]) == 1)
            sad++;
    
    for (int i = 0; i < n;)
    {
        if (a[i] == 1)
        {
            i++;
            continue;
        }
        int run = 0;
        
        while (i + 1 < n && a[i + 1] != 1)
        {
            if (gcdll(a[i], a[i + 1]) == 1)
                run++;
            else
            {
                two += run / 2;
                run = 0;
            }
            i++;
        }
        two += run / 2;
        i++;
    }
    
    int *ones = malloc((size_t)n * sizeof *ones)
        , oc = 0;
    
    for (int i = 0; i < n;)
    {
        if (a[i] != 1)
        {
            i++;
            continue;
        }
        int l = i;
        
        while (i < n && a[i] == 1)
            i++;
        if (l > 0 && i < n)
        {
            ones[oc] = i - l;
            oc++;
        }
    }

    int use = k < two ? k : two;
    sad -= 2 * use;
    k -= use;
    qsort(ones, oc, sizeof *ones, cmpi);

    for (int i = 0; i < oc && ones[i] <= k; i++)
    {
        k -= ones[i];
        sad -= ones[i] + 1;
    }
    if (k > sad)
        k = sad;
    sad -= k;
    if (sad < 0)
        sad = 0;
    
    free(ones);
    return sad;
}
// int main(void)
// {
//     int T;
//     if (scanf("%d", &T) != 1)
//         return 0;
//     while (T--)
//     {
//         int n, k;
//         scanf("%d%d", &n, &k);
//         i64 *a = malloc((size_t)n * sizeof *a);
//         for (int i = 0; i < n; i++)
//             scanf("%lld", &a[i]);
//         printf("%d\n", solver(n, k, a));
//         free(a);
//     }
//     return 0;
// }
