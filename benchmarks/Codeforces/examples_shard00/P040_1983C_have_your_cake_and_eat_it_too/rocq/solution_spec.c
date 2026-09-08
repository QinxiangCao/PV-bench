/* Codeforces 1983/C - Have Your Cake and Eat It Too */
// #include <stdio.h>
// #include <stdlib.h>
#include "array2_ext_def.h"

/*@ Extern Coq
      (Pre : list Z -> list Z -> list Z -> Prop)
      (Int64PtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
      (Int64PtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too.rocq.spec_lib */

static int try_order(long long **v, int n, long long need, const int order[3], int out[6])

{
    int left[3] = {0, 0, 0}, right[3] = {0, 0, 0}, pos = 0;
    
    for (int part = 0; part < 2; ++part)
    {
        int who = order[part], start = pos;
        long long acc = 0;

        while (pos < n && acc < need)
        {
            acc += v[who][pos];
            ++pos;
        }
        
        if (acc < need)
        {
            
            return 0;
        }
        left[who] = start + 1;
        right[who] = pos;
    }
    int who = order[2];
    long long acc = 0;

    for (int i = pos; i < n; ++i)
        acc += v[who][i];
    
    if (acc < need)
    {
        
        return 0;
    }
    left[who] = pos + 1;
    right[who] = n;

    for (int i = 0; i < 3; ++i)
    {
        out[2 * i] = left[i];
        out[2 * i + 1] = right[i];
    }
    
    return 1;
}

/*@ Extern Coq
      (Pre : list Z -> list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> option (list Z) -> Prop)
      (Int64PtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too.rocq.spec_lib */

/*@ Extern Coq
      (Int64PtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
static int
solver(long long **v, int n,
       int out[6]) 

/*@ With (a : list Z)
             (b : list Z)
             (c : list Z)
    Require
      3 <= Zlength(a) && Zlength(a) <= 200000 &&
      Zlength(b) == Zlength(a) &&
      Zlength(c) == Zlength(a) &&
      (forall row col,
        (0 <= row && row < 3 && 0 <= col && col < Zlength(a)) =>
          (1 <= Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) &&
           Znth(col, Znth(row, cons(a, cons(b, cons(c, nil))), nil), 0) <= 1000000)) &&
      Pre(a, b, c) &&
      n == Zlength(a) &&
      Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) *
      IntArray::undef_full(out, 6)
    Ensure
      ((__return == 0 && Spec(a, b, c, None) &&
      Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) * IntArray::undef_full(out, 6)) ||
       (__return == 1 && exists result raw_result,
          Spec(a, b, c, Some(result)) &&
          (forall i, (0 <= i && i < 6) => raw_result[i] == result[i] + 1) &&
        Int64PtrArray2::full(v, 3, cons(a, cons(b, cons(c, nil)))) * IntArray::full(out, 6, raw_result)))
*/

{
    const int orders[18] = {0, 1, 2, 0, 2, 1, 1, 0, 2, 1, 2, 0, 2, 0, 1, 2, 1, 0};
    long long total = 0;
    
    long long *row0 = v[0];
    
    for (int i = 0; i < n; ++i)
        total += row0[i];
    
    long long need = (total + 2) / 3;
    
    for (int z = 0; z < 6; ++z)
    {
        const int *ordp = orders + 3 * z;
        
        int ok = try_order(v, n, need, ordp, out)
            ;
        if (ok)
        {
            
            return 1;
        }
        
    }
    
    return 0;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n);
//         long long *v[3]; int out[6];
//         for (int p = 0; p < 3; ++p) {
//             v[p] = malloc((size_t)n * sizeof(**v));
//             for (int i = 0; i < n; ++i) scanf("%lld", &v[p][i]);
//         }
//         int ok = solver(v, n, out);
//         if (!ok) puts("-1");
//         else printf("%d %d %d %d %d %d\n", out[0], out[1], out[2], out[3], out[4], out[5]);
//         for (int p = 0; p < 3; ++p) free(v[p]);
//     }
//     return 0;
// }
