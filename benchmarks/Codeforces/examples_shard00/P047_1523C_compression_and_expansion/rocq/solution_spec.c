/* Codeforces 1523/C - Compression and Expansion */
// #include <stdio.h>
// #include <stdlib.h>

/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> list (list Z) -> Prop)
      (concat : list (list Z) -> list Z)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion.rocq.spec_lib */
/*@ Extern Coq
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
*/

static int solver(const int *values, int n, int *flat,
                  int *lengths) 

/*@ With (last_numbers : list Z)
    Require
      1 <= Zlength(last_numbers) && Zlength(last_numbers) <= 1000 &&
      (forall i, (0 <= i && i < Zlength(last_numbers)) => (1 <= last_numbers[i] && last_numbers[i] <= Zlength(last_numbers))) &&
      Pre(last_numbers) &&
      n == Zlength(last_numbers) &&
      IntArray::full(values, n, last_numbers) *
      IntArray::undef_full(flat, n * n) * IntArray::undef_full(lengths, n)
    Ensure
      exists result lengths_data,
        Spec(last_numbers, result) &&
        (forall i, (0 <= i && i < n) => lengths_data[i] == Zlength(result[i])) &&
        __return == Zlength(concat(result)) &&
        IntArray::full(values, n, last_numbers) *
        IntArray::full(flat, Zlength(concat(result)), concat(result)) *
        IntArray::undef_seg(flat, Zlength(concat(result)), n * n) *
        IntArray::full(lengths, n, lengths_data)
*/

{
    int stack[1005], depth = 0, total = 0;
    
    for (int line = 0; line < n; ++line)
    {
        int x = values[line];
        if (x == 1)
        {
            stack[depth] = 1;
            ++depth;
        }
        else
        {
            
            while (depth && stack[depth - 1] + 1 != x)
                --depth;
            stack[depth - 1] = x;
        }
        
        lengths[line] = depth;
        
        for (int i = 0; i < depth; ++i)
        {
            
            flat[total] = stack[i];
            ++total;
        }
    }
    
    return total;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); int *values = malloc((size_t)n * sizeof(*values));
//         int *lengths = malloc((size_t)n * sizeof(*lengths)); int *flat = malloc((size_t)n * n * sizeof(*flat));
//         for (int i = 0; i < n; ++i) scanf("%d", &values[i]); solver(values, n, flat, lengths);
//         int at = 0; for (int line = 0; line < n; ++line)
//             for (int i = 0; i < lengths[line]; ++i) printf("%d%c", flat[at++], i + 1 == lengths[line] ? '\n' : '.');
//         free(flat); free(lengths); free(values);
//     }
//     return 0;
// }
