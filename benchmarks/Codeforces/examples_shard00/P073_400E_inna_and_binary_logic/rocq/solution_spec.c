/* Codeforces 400/E - Inna and Binary Logic */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;
/* Trusted, success-only allocator models: verification assumes these calls
 * return fresh non-NULL storage. Standard C allocation may fail; these
 * contracts do not prove absence of out-of-memory failures.
 * The conservative byte bound covers every allocation made by this case. */
void *malloc(size_t size)
/*@ With (cap : Z)
    Require
      0 < cap &&
      size == cap * sizeof(int) &&
      size <= INT_MAX
    Ensure
      __return != 0 &&
      IntArray::undef_full(__return, cap)
*/;

void *calloc(size_t count, size_t size)
/*@ calloc_int
    Require
      0 < count && count * size <= INT_MAX &&
      size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, count, repeat_Z(0, count))
*/
/*@ calloc_int64
    Require
      0 < count && count * size <= INT_MAX &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, count, repeat_Z(0, count))
*/;
void free(void *ptr)
/*@ free_int
    With (cap : Z) (contents : list Z)
    Require IntArray::full(ptr, cap, contents)
    Ensure emp
*/
/*@ free_int64
    With (cap : Z) (contents : list Z)
    Require Int64Array::full(ptr, cap, contents)
    Ensure emp
*/;
#define NULL 0
#define BITS 17
static int n, *pref, *suff, *len;
static long long *cnt;
#define IX(bit, node) ((size_t)(bit) * 4 * n + (node))
/*@ Extern Coq
      (P073Summary : Z -> list Z -> Z -> Z -> Z -> Prop)
      (P073Layout : Z -> Z -> Z -> Z -> Prop)
      (P073Tree : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073ZeroTree : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073OutsideTree : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073NodePrefix : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073NodeFrame : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073BufferBounds : Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (P073Weighted : list Z -> Z -> Z)
      (P073History : list Z -> list (Z * Z) -> Z -> list Z -> list Z -> Prop)
      (ApplyPointUpdate : list Z -> Z * Z -> list Z)
*/

static void pull(int v)

{
    
    for (int b = 0; b < BITS; ++b)
    {
        int L = v * 2, R = L + 1;
        
        pref[IX(b, v)] = pref[IX(b, L)] + (pref[IX(b, L)] == len[L] ? pref[IX(b, R)] : 0);
        suff[IX(b, v)] = suff[IX(b, R)] + (suff[IX(b, R)] == len[R] ? suff[IX(b, L)] : 0);
        cnt[IX(b, v)] = cnt[IX(b, L)] + cnt[IX(b, R)] + (long long)suff[IX(b, L)] * pref[IX(b, R)];
    }
}
static void build(int v, int l, int r, const int *a)

{
    len[v] = r - l;
    if (r - l == 1)
    {
        
        for (int b = 0; b < BITS; ++b)
            if ((a[l] >> b) & 1)
            {
                cnt[IX(b, v)] = 1;
                suff[IX(b, v)] = 1;
                pref[IX(b, v)] = 1;
            }
        return;
    }
    int m = (l + r) / 2;
    build(v * 2, l, m, a) ;
    build(v * 2 + 1, m, r, a) ;
    pull(v) ;
}
static void update(int v, int l, int r, int p, int x)

{
    if (r - l == 1)
    {
        
        for (int b = 0; b < BITS; ++b)
        {
            int on = (x >> b) & 1;
            suff[IX(b, v)] = on;
            pref[IX(b, v)] = on;
            cnt[IX(b, v)] = on;
        }
        return;
    }
    int m = (l + r) / 2;
    if (p < m)
        update(v * 2, l, m, p, x) ;
    else
        update(v * 2 + 1, m, r, p, x) ;
    pull(v) ;
}
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : list Z -> list (Z * Z) -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
*/

static void solver(int size, const int *input, int m, const int *positions, const int *values,
                   long long *out) 
/*@ With (initial_a : list Z)
             (updates : list (Z * Z))
             (positions_data values_data : list Z)
    Require
      1 <= Zlength(initial_a) && Zlength(initial_a) <= 100000 &&
      1 <= Zlength(updates) && Zlength(updates) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(initial_a)) => (0 <= initial_a[i] && initial_a[i] <= 100000)) &&
      (forall i, (0 <= i && i < Zlength(updates)) => ((0 <= fst(updates[i]) && fst(updates[i]) < Zlength(initial_a)) && (0 <= snd(updates[i]) && snd(updates[i]) <= 100000))) &&
      size == Zlength(initial_a) && m == Zlength(updates) &&
      Zlength(positions_data) == m && Zlength(values_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (fst(updates[i]) == positions_data[i] &&
         snd(updates[i]) == values_data[i])) &&
      IntArray::full(input, size, initial_a) *
      IntArray::full(positions, m, positions_data) *
      IntArray::full(values, m, values_data) *
      Int64Array::undef_full(out, m) *
      undef_data_at(&n, int) *
      undef_data_at(&pref, int *) *
      undef_data_at(&suff, int *) *
      undef_data_at(&cnt, long long *) *
      undef_data_at(&len, int *)
    Ensure
      exists result,
        Spec(initial_a, updates, result) &&
        IntArray::full(input, size, initial_a) *
        IntArray::full(positions, m, positions_data) *
        IntArray::full(values, m, values_data) *
        Int64Array::full(out, m, result) *
        data_at(&n, int, size) *
        data_at(&pref, int *, 0) *
        data_at(&suff, int *, 0) *
        data_at(&cnt, long long *, 0) *
        data_at(&len, int *, 0)
*/
{
    n = size;
    
    //@ Given original
    int *a = malloc((size_t)n * sizeof(*a)) ;
    
    for (int i = 0; i < n; ++i)
        a[i] = input[i];
    
    size_t all = (size_t)BITS * 4 * n;
    pref = calloc(all, sizeof(*pref)) ;
    suff = calloc(all, sizeof(*suff)) ;
    cnt = calloc(all, sizeof(*cnt)) ;
    len = calloc((size_t)4 * n, sizeof(*len)) ;
    
    build(1, 0, n, a) ;
    
    for (int i = 0; i < m; ++i)
    {
        //@ Given current from cur
        //@ Given completed from result
        int p = positions[i], v = values[i];
        a[p] = v;
        update(1, 0, n, p, v) ;
        long long ans = 0;
        
        for (int b = 0; b < BITS; ++b)
            ans += cnt[IX(b, 1)] * (1 << b);
        out[i] = ans;
    }
    //@ Given final_values from cur
    //@ Given final_prefix from pr
    //@ Given final_suffix from su
    //@ Given final_counts from ct
    //@ Given final_lengths from ln
    free(a) ;
    free(pref) ;
    free(suff) ;
    free(cnt) ;
    free(len) ;
    len = NULL;
    suff = NULL;
    pref = NULL;
    cnt = NULL;
}
// int main(void)
// {
//     int size, m;
//     if (scanf("%d %d", &size, &m) != 2)
//         return 0;
//     int *a = malloc((size_t)size * sizeof(*a)), *positions = malloc((size_t)m * sizeof(*positions)),
//         *values = malloc((size_t)m * sizeof(*values));
//     long long *out = malloc((size_t)m * sizeof(*out));
//     for (int i = 0; i < size; ++i)
//         scanf("%d", &a[i]);
//     for (int i = 0; i < m; ++i)
//     {
//         scanf("%d %d", &positions[i], &values[i]);
//         --positions[i];
//     }
//     solver(size, a, m, positions, values, out);
//     for (int i = 0; i < m; ++i)
//         printf("%lld\n", out[i]);
//     free(a);
//     free(positions);
//     free(values);
//     free(out);
//     return 0;
// }
