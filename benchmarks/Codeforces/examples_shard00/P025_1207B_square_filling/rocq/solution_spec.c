/* Codeforces 1207/B - Square Filling */
// #include <stdio.h>
#include "array2_ext_def.h"

typedef struct
{
    int r, c;
} Operation;

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> Z -> list (list Z) -> option (list (Z * Z)) -> Prop)
*/

/*@ Extern Coq
      (ScanOperations : Z -> Z -> list (list Z) -> Z -> Z -> list (Z * Z) -> Prop)
      (made_state : list (Z * Z) -> list Z)
      (staged_ops : list (Z * Z) -> list (option Z))
      (CheckedPrefix : Z -> Z -> list (list Z) -> list (Z * Z) -> Z -> Z -> Prop)
*/
static int solver(int n, int m, const int a[50][50],
                  Operation *ops) 
/*@ With (matrix : list (list Z))
             (matrix_mem : list (list (option Z)))
    Require
      2 <= n && n <= 50 &&
      2 <= m && m <= 50 &&
      Zlength(matrix) == n &&
      (forall i, (0 <= i && i < n) => Zlength(matrix[i]) == m) &&
      (forall i j, (0 <= i && i < n && 0 <= j && j < m) =>
        ((Znth(j, Znth(i, matrix, nil), 0) == 0) ||
         (Znth(j, Znth(i, matrix, nil), 0) == 1))) &&
      Zlength(matrix_mem) == 50 &&
      (forall i, (0 <= i && i < 50) =>
        Zlength(Znth(i, matrix_mem, nil)) == 50) &&
      (forall i, (0 <= i && i < n) =>
        (forall j, (0 <= j && j < m) =>
          Znth(j, Znth(i, matrix_mem, nil), None) ==
            Some(Znth(j, Znth(i, matrix, nil), 0)))) &&
      IntArray2::mixed_full(a, 50, 50, matrix_mem) *
      IntArray::undef_full(ops, 5000)
    Ensure
      exists ops_mem,
        ((__return == -1 && Spec(n, m, matrix, None)) ||
         (exists result,
            Spec(n, m, matrix, Some(result)) && __return == Zlength(result) &&
            (forall i, (0 <= i && i < __return) =>
              (ops_mem[2 * i] == Some(fst(result[i]) + 1) &&
               ops_mem[2 * i + 1] == Some(snd(result[i]) + 1))))) &&
        IntArray2::mixed_full(a, 50, 50, matrix_mem) *
        IntArray::mixed_full(ops, 5000, ops_mem)
*/

{
    int made[50 * 50] = {0}, count = 0;

    for (int i = 0; i + 1 < n; ++i)
        
        for (int j = 0; j + 1 < m; ++j)
        {
            if (a[i][j] && a[i + 1][j] && a[i][j + 1] && a[i + 1][j + 1])
            {
                
                ((int *)ops)[2 * count] = i + 1;
                ((int *)ops)[2 * count + 1] = j + 1;
                count++;
                
                made[i * 50 + j] = 1;
                made[(i + 1) * 50 + j] = 1;
                made[i * 50 + (j + 1)] = 1;
                made[(i + 1) * 50 + (j + 1)] = 1;
            }
        }
    
    for (int i = 0; i < n; ++i)
        
        for (int j = 0; j < m; ++j)
            if (a[i][j] != made[i * 50 + j])
                return -1;
    return count;
}

// int main(void)
// {
//     int n, m, a[50][50]; Operation ops[2500];
//     if (scanf("%d %d", &n, &m) != 2) return 0;
//     for (int i = 0; i < n; ++i)
//         for (int j = 0; j < m; ++j) scanf("%d", &a[i][j]);
//     int count = solver(n, m, a, ops);
//     if (count < 0) { puts("-1"); return 0; }
//     printf("%d\n", count);
//     for (int i = 0; i < count; ++i) printf("%d %d\n", ops[i].r, ops[i].c);
//     return 0;
// }
