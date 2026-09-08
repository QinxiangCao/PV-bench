/*@ Import Lean
import Codeforces.examples_shard01.P005_707A_brains_photos.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 707/A - Brain's Photos  (rating 800, IMPLEMENTATION)
 *
 * The photo is coloured iff at least one pixel is cyan, magenta or yellow;
 * white / grey / black alone make it black-and-white.
 */

// #include <stdio.h>
/*@ Extern Coq (bool :: *) */
/*@ Extern Coq
      (Spec : list (list Z) -> bool -> Prop)
      (SolverReturnBridge : bool -> Z -> Prop)
      (concat : {A} -> list (list A) -> list A)
*/
/* solver: pure.  px holds n*m pixel letters; 1 if the photo is coloured. */

static int solver(const char *px, int n, int m)
/*@ With (photo : list (list Z))
    Require
      1 <= n && n <= 100 &&
      1 <= m && m <= 100 &&
      n == Zlength(photo) &&
      (forall i, (0 <= i && i < n) => Zlength(photo[i]) == m) &&
      (forall i, (0 <= i && i < n) =>
        (forall j, (0 <= j && j < m) =>
          (photo[i][j] == 67 || photo[i][j] == 77 ||
           photo[i][j] == 89 || photo[i][j] == 87 ||
           photo[i][j] == 71 || photo[i][j] == 66))) &&
      CharArray::full(px, n * m, concat(photo))
    Ensure
      exists (out : bool),
        Spec(photo, out) &&
        SolverReturnBridge(out, __return) && CharArray::full(px, n * m, concat(photo))
*/
{
    for (int i = 0; i < n * m; i++)
        if (px[i] == 'C' || px[i] == 'M' || px[i] == 'Y')
            return 1;
    return 0;
}

// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     static char px[10005];
//     for (int i = 0; i < n * m; i++)
//         scanf(" %c", &px[i]);
//     puts(solver(px, n, m) ? "#Color" : "#Black&White");
//     return 0;
// }
