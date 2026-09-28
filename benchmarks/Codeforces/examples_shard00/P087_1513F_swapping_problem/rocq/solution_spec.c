// #include <stdio.h>
// #include <stdlib.h>
typedef long long i64;
typedef struct
{
    int l, r;
} Seg;

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Permutation : list (Z * Z) -> list (Z * Z) -> Prop)
      (SegmentAllocationSize : Z -> Z -> Prop)
      (SegmentsProper : list (Z * Z) -> Prop)
      (SegmentsBounded : list (Z * Z) -> Prop)
      (SegmentsSortedByLeft : list (Z * Z) -> Prop)
      (SolverScanState : list Z -> list Z -> Z -> Z ->
                         list (Z * Z) -> list (Z * Z) -> Prop)
      (DirectedOverlapMaximumPrefix : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Prop)
      (DirectedOverlapMaximum : list (Z * Z) -> list (Z * Z) -> Z -> Prop)
      (PrefixRightMaxima : list (Z * Z) -> list Z -> Z -> Prop)
      (UpperBoundBracket : list (Z * Z) -> Z -> Z -> Z -> Prop)
      (SwappingOverlapMaximum : list Z -> list Z -> Z -> Prop)
      (PairDistanceSum : list Z -> list Z -> Z)
      (SegArray::full : Z -> Z -> list (Z * Z) -> Assertion)
      (SegArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
*/

void *malloc(unsigned long size)
/*@ malloc_seg
    With (capacity : Z)
    Require
      0 <= capacity && SegmentAllocationSize(size, capacity)
    Ensure
      __return != 0 && SegArray::undef_full(__return, capacity)
*/
/*@ malloc_int
    With (capacity : Z)
    Require
      0 <= capacity && size == capacity * sizeof(int)
    Ensure
      __return != 0 && IntArray::undef_full(__return, capacity)
*/;

void free(void *ptr)
/*@ free_int
    With (capacity : Z)
    Require
      exists values,
        Zlength(values) == capacity && IntArray::full(ptr, capacity, values)
    Ensure emp
*/
/*@ free_seg_mixed
    With (capacity : Z) (count : Z) (values : list (Z * Z)) (tail : Z)
    Require
      0 <= count && count <= capacity && Zlength(values) == count &&
      SegArray::full(ptr, count, values) *
      SegArray::undef_full(tail, capacity - count)
    Ensure emp
*/;

void qsort(Seg *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
;

static int cmp(const void *A, const void *B)
{
    const Seg *a = A, *b = B;
    return a->l == b->l ? a->r - b->r : a->l - b->l;
}
static int overlap(Seg *a, int na, Seg *b, int nb)

{
    if (!na || !nb)
        return 0;
    qsort(b, nb, sizeof *b, cmp)
        ;
    int *pref = malloc(nb * sizeof *pref)
        ;
    
    for (int i = 0; i < nb; i++)
        
        pref[i] = i && pref[i - 1] > b[i].r ? pref[i - 1] : b[i].r;
    int best = 0;
    
    for (int i = 0; i < na; i++)
    {
        int lo = 0, hi = nb;
        
        while (lo < hi)
        {
            int md = (lo + hi) / 2;
            
            if (b[md].l <= a[i].l)
                lo = md + 1;
            else
                hi = md;
        }
        
        if (lo)
        {
            int x = pref[lo - 1] < a[i].r ? pref[lo - 1] : a[i].r;
            x -= a[i].l;
            if (x > best)
                best = x;
        }
    }
    free(pref) ;
    return best;
}
/*@ Extern Coq
      (Spec : list Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/

/*@ Extern Coq
      (IncreasingIntervals : list Z -> list Z -> Z -> list (Z * Z))
      (DecreasingIntervals : list Z -> list Z -> Z -> list (Z * Z))
*/
static i64 solver(int n, const int *a,
                  const int *b) 
/*@ With (values : list Z)
             (b_data : list Z)
    Require
      1 <= Zlength(values) && Zlength(values) <= 200000 &&
      Zlength(b_data) == Zlength(values) &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 1000000000)) &&
      (forall i, (0 <= i && i < Zlength(b_data)) => (1 <= b_data[i] && b_data[i] <= 1000000000)) &&
      n == Zlength(values) &&
      IntArray::full(a, n, values) * IntArray::full(b, n, b_data)
    Ensure
      Spec(values, b_data, __return) &&
      IntArray::full(a, n, values) * IntArray::full(b, n, b_data)
*/
{
    Seg *x = malloc(n * sizeof *x) ,
        *y = malloc(n * sizeof *y) ;
    int nx = 0, ny = 0;
    i64 base = 0;
    
    for (int i = 0; i < n; i++)
    {
        int d = a[i] - b[i];
        if (d < 0)
        {
            
            base -= d;
            x[nx].l = a[i];
            x[nx].r = b[i];
            nx++;
        }
        else if (d > 0)
        {
            
            base += d;
            y[ny].l = b[i];
            y[ny].r = a[i];
            ny++;
        }
    }
    
    int p = overlap(x, nx, y, ny)
        ,
        q = overlap(y, ny, x, nx),
        best = p > q ? p : q;
    
    free(y) ;
    free(x) ;
    return base - 2LL * best;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     int *a = malloc(n * sizeof *a), *b = malloc(n * sizeof *b);
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     for (int i = 0; i < n; i++)
//         scanf("%d", &b[i]);
//     printf("%lld\n", solver(n, a, b));
//     free(b);
//     free(a);
//     return 0;
// }
