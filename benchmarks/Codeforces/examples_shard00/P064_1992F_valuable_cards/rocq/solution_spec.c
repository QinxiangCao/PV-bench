/* Codeforces 1992/F - Valuable Cards */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"

typedef unsigned long size_t;

/*@ Extern Coq
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (UCharArray::full : Z -> Z -> list Z -> Assertion)
*/

/*@ Extern Coq
      (ValuableOuterState : Z -> list Z -> Z -> Z -> list Z -> Prop)
      (ValuableClosureState : Z -> list Z -> Z -> list Z -> Z -> list Z -> Z -> Prop)
      (ValuableBitmap : Z -> list Z -> list Z -> Prop)
      (ValuableClearingState : Z -> list Z -> Z -> list Z -> Prop)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::seg_shape : Z -> Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (ValuableForcedHistory : Z -> list Z -> Z -> Z -> list Z -> Prop)
*/

/*@ Extern Coq
      (ValuableAlignedHistory : Z -> list Z -> Z -> Z -> list Z -> Prop)
*/

void *calloc(unsigned long nmemb, unsigned long size)
/*@ calloc_uchar
    With (cells : Z)
    Require
      0 <= cells && cells <= INT_MAX &&
      nmemb == cells && size == 1
    Ensure
      __return != 0 &&
      UCharArray::full(__return, cells, repeat_Z(0, cells))
*/;

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
/*@ free_uchar
    With (cells : Z) (values : list Z)
    Require
      0 <= cells && Zlength(values) == cells &&
      UCharArray::full(ptr, cells, values)
    Ensure emp
*/
/*@ free_int_split
    With (cap : Z) (count : Z) (values : list Z)
    Require
      0 <= count && count <= cap && Zlength(values) == count &&
      IntArray::seg(ptr, 0, count, values) *
      IntArray::undef_seg(ptr, count, cap)
    Ensure emp
*/;

static int solver(const int *a, int n,
                  int x) 
/*@ With (values : list Z)
    Require
      2 <= x && x <= 100000 &&
      1 <= Zlength(values) && Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 200000)) &&
      Pre(x, values) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(x, values, __return) && IntArray::full(a, n, values)
*/
{
    unsigned char *used = calloc((size_t)x + 1, 1)
        ;
    int *products_buf = malloc((size_t)(x + 1) * sizeof(*products_buf))
        ;
    int count = 1, segments = 1;
    products_buf[0] = 1;
    used[1] = 1;
    
    for (int i = 0; i < n; ++i)
    {
        int v = a[i];
        if (x % v)
            continue;
        int old = count, reaches = 0;
        
        for (int j = 0; j < old; ++j)
            
            if (products_buf[j] <= x / v && x % (products_buf[j] * v) == 0)
            {
                int p = products_buf[j] * v;
                
                if (!used[p])
                {
                    used[p] = 1;
                    products_buf[count] = p;
                    
                    ++count;
                }
                if (p == x)
                    reaches = 1;
            }
        
        if (reaches)
        {
            ++segments;
            
            for (int j = 0; j < count; ++j)
                used[products_buf[j]] = 0;
            count = 1;
            products_buf[0] = 1;
            used[1] = 1;

            if (!used[v])
            {
                used[v] = 1;
                products_buf[count] = v;
                
                ++count;
            }
        }
    }
    
    free(used)
        ;
    free(products_buf)
        ;
    return segments;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n, x;
//         scanf("%d %d", &n, &x);
//         int *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i)
//             scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n, x));
//         free(a);
//     }
//     return 0;
// }
