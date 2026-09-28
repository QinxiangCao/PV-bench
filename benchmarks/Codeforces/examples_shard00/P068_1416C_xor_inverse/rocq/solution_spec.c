/* Codeforces 1416/C - XOR Inverse */
// #include <stdio.h>
// #include <stdlib.h>
static int *a, *tmp;
static long long cost[30][2];
/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Spec : list Z -> Z * Z -> Prop)
      (SolveEffect : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Prop)
      (CostBound : list (list Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (Int64Array2::undef_full : Z -> Z -> Z -> Assertion)
      (Int64Array2::full : Z -> Z -> Z -> list (list Z) -> Assertion)
*/

/*@ Extern Coq
      (SolveCountPrefix : list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StablePartitionPrefix : list Z -> list (option Z) -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PartitionCopyBack : list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (InputCopyPrefix : list Z -> list (option Z) -> Z -> Prop)
      (ZeroCostPrefix : list (list (option Z)) -> Z -> Prop)
      (XorChoicePrefix : list Z -> list (list Z) -> Z -> Z -> Z -> Prop)
      (CostArrayMixed : Z -> Z -> Z -> list (list (option Z)) -> Assertion)
*/
static void solve(int l, int r, int bit)

{
    if (bit < 0 || r - l <= 1)
        return;
    long long zeros = 0, ones = 0;
    
    for (int i = l; i < r; i = i + 1)
    {
        if ((a[i] >> bit) & 1)
        {
            cost[bit][1] += zeros;
            ones = ones + 1;
        }
        else
        {
            cost[bit][0] += ones;
            zeros = zeros + 1;
        }
    }
    int p = l;
    
    for (int i = l; i < r; i = i + 1)
    {
        if (((a[i] >> bit) & 1) == 0)
        {
            tmp[p] = a[i];
            p = p + 1;
        }
    }
    int mid = p;
    
    for (int i = l; i < r; i = i + 1)
    {
        if ((a[i] >> bit) & 1)
        {
            
            tmp[p] = a[i];
            p = p + 1;
        }
    }
    
    for (int i = l; i < r; i = i + 1)
    {

        int value = tmp[i];
        
        a[i] = value;
    }
    solve(l, mid, bit - 1)
        ;
    
    solve(mid, r, bit - 1)
        ;
}
typedef unsigned long size_t;

void *malloc(size_t size)
/*@ malloc_int
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure exists cells,
      __return != 0 && Zlength(cells) == cap &&
      IntArray::mixed_full(__return, cap, cells)
*/;

void free(void *ptr)
/*@ free_int
    With (cap : Z)
    Require 0 <= cap && IntArray::undef_full(ptr, cap)
    Ensure emp
*/;

static void solver(const int *input, int n, long long *out_inv,
                   int *out_x) 
/*@ With (input_values : list Z) (a_before tmp_before : Z)
    Require
      1 <= Zlength(input_values) && Zlength(input_values) <= 300000 &&
      (forall i, (0 <= i && i < Zlength(input_values)) =>
        (0 <= input_values[i] && input_values[i] <= 1000000000)) &&
      n == Zlength(input_values) &&
      IntArray::full(input, n, input_values) *
      Int64Array2::undef_full(cost, 30, 2) *
      store(&a, int *, a_before) * store(&tmp, int *, tmp_before) *
      undef_data_at(out_inv) * undef_data_at(out_x)
    Ensure
      exists inv x cost_post,
        Spec(input_values, pair(inv, x)) &&
        IntArray::full(input, n, input_values) *
        Int64Array2::full(cost, 30, 2, cost_post) *
        store(&a, int *, 0) * store(&tmp, int *, 0) *
        store(out_inv, long long, inv) * store(out_x, int, x)
*/
{
    a = malloc((size_t)n * sizeof(*a))
        ;
    tmp = malloc((size_t)n * sizeof(*tmp))
        ;
    
    for (int i = 0; i < n; i = i + 1)
        a[i] = input[i];
    
    for (int b = 0; b < 30; b = b + 1)
    {
        
        cost[b][1] = 0;
        cost[b][0] = 0;
    }
    
    solve(0, n, 29) ;
    long long inv = 0;
    int x = 0;
    
    for (int b = 0; b < 30; b = b + 1)
    {
        
        if (cost[b][1] < cost[b][0])
        {
            inv += cost[b][1];
            x |= 1 << b;
        }
        else
            inv += cost[b][0];
    }
    *out_inv = inv;
    *out_x = x;
    
    free(a) ;
    free(tmp) ;
    a = 0;
    tmp = 0;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     int *input = malloc((size_t)n * sizeof(*input));
//     for (int i = 0; i < n; ++i)
//         scanf("%d", &input[i]);
//     long long inv;
//     int x;
//     solver(input, n, &inv, &x);
//     printf("%lld %d\n", inv, x);
//     free(input);
//     return 0;
// }
