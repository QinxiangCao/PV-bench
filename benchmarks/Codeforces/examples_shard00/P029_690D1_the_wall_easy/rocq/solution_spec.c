/* Codeforces 690/D1 - The Wall (easy) */
// #include <stdio.h>
#include "array2_ext_def.h"

/*@ Extern Coq
      (Spec : Z -> Z -> list (list Z) -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P029_690D1_the_wall_easy.rocq.spec_lib */

static int solver(const char grid[][105], int r, int c)

/*@ With (grid_data : list (list Z))
             (grid_mem : list (list (option Z)))
    Require
      1 <= r && r <= 100 &&
      1 <= c && c <= 100 &&
      Zlength(grid_data) == r &&
      (forall i, (0 <= i && i < r) => Zlength(grid_data[i]) == c) &&
      (forall i j, (0 <= i && i < r && 0 <= j && j < c) =>
        ((Znth(j, Znth(i, grid_data, nil), 0) == 66) ||
         (Znth(j, Znth(i, grid_data, nil), 0) == 46))) &&
      Zlength(grid_mem) == r &&
      (forall i, (0 <= i && i < r) =>
        (Zlength(Znth(i, grid_mem, nil)) == 105 &&
         (forall j, (0 <= j && j < c) =>
           Znth(j, Znth(i, grid_mem, nil), None) ==
             Some(Znth(j, Znth(i, grid_data, nil), 0))) &&
         Znth(c, Znth(i, grid_mem, nil), None) == Some(0))) &&
      CharArray2::mixed_full(grid, r, 105, grid_mem)
    Ensure
      Spec(r, c, grid_data, __return) &&
      CharArray2::mixed_full(grid, r, 105, grid_mem)
*/

{
    int occupied[100] = {0};
    
    for (int i = 0; i < r; ++i)
        
        for (int j = 0; j < c; ++j) {

            if (grid[i][j] == 'B') occupied[j] = 1;
            
        }
    int segments = 0;
    
    for (int j = 0; j < c; ++j)
        if (occupied[j] && (j == 0 || !occupied[j - 1])) ++segments;
    return segments;
}

// int main(void)
// {
//     int r, c; char grid[100][105];
//     if (scanf("%d %d", &r, &c) != 2) return 0;
//     for (int i = 0; i < r; ++i) scanf("%104s", grid[i]);
//     printf("%d\n", solver(grid, r, c));
//     return 0;
// }
