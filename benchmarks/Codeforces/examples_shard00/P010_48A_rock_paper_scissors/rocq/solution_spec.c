/* Codeforces 48/A - Rock-paper-scissors */
// #include <stdio.h>
#include "string.h"
#include "array2_ext_def.h"

/*@ Extern Coq
      (Pre : list Z -> list Z -> list Z -> Prop)
*/

static int beats(const char g[3][16], int ia, int ib)

{

    char ac = g[ia][0];

    char bc = g[ib][0];

    return (ac == 'r' && bc == 's') ||
           (ac == 's' && bc == 'p') ||
           (ac == 'p' && bc == 'r');
}

/*@ Extern Coq
      (Pre : list Z -> list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors.rocq.spec_lib */

static char solver(const char g[3][16])

/*@ With (players : list (list Z))
             (game_mem : list (list (option Z)))
    Require
      Zlength(players) == 3 &&
      Pre(Znth(0, players, nil), Znth(1, players, nil), Znth(2, players, nil)) &&
      Zlength(game_mem) == 3 &&
      (forall i, (0 <= i && i < 3) =>
        (Zlength(Znth(i, players, nil)) < 16 &&
         Zlength(Znth(i, game_mem, nil)) == 16 &&
         (forall j, (0 <= j && j < Zlength(Znth(i, players, nil))) =>
           Znth(j, Znth(i, game_mem, nil), None) ==
             Some(Znth(j, Znth(i, players, nil), 0))) &&
         Znth(Zlength(Znth(i, players, nil)), Znth(i, game_mem, nil), None) == Some(0))) &&
      CharArray2::mixed_full(g, 3, 16, game_mem)
    Ensure
      exists result,
        Spec(Znth(0, players, nil), Znth(1, players, nil),
             Znth(2, players, nil), result) && __return == result[0] &&
        CharArray2::mixed_full(g, 3, 16, game_mem)
*/

{
    
    for (int i = 0; i < 3; ++i)
        if (beats(g, i, (i + 1) % 3)
               &&
            beats(g, i, (i + 2) % 3)
              )
            return i == 0 ? 'F' : (i == 1 ? 'M' : 'S');
    return '?';
}

// int main(void)
// {
//     char g[3][16];
//     if (scanf("%15s %15s %15s", g[0], g[1], g[2]) != 3) return 0;
//     printf("%c\n", solver(g));
//     return 0;
// }
