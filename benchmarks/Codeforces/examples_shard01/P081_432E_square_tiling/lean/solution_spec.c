/*@ Import Lean
import Codeforces.examples_shard01.P081_432E_square_tiling.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 432/E - Square Tiling  (rating 2300, GREEDY)
 *
 * Fill the cells in reading order.  An empty cell takes the smallest letter
 * that clashes with none of its already painted neighbours — squares placed
 * earlier can sit above, to the left, and (having grown downwards) also to the
 * right or below.  Then grow the square while it stays inside the table,
 * covers only empty cells, keeps every neighbouring cell legal, and actually
 * helps: that is, while the next cell of this row would otherwise be forced to
 * take a bigger letter.
 */

// #include <stdio.h>
// #include <stdlib.h>

/*@ Extern Coq
      (Spec : Z -> Z -> list(list Z) -> Prop)
      (concat : {A} -> list(list A) -> list A)
*/

#define MAXN 105

/* conflicts: is colour c already used by a painted neighbour of (i,j)?
 * left_override replaces the left neighbour when it is about to become c. */
static int conflicts(const char *g, int n, int m,
                     int i, int j, char c, char left_override)
{
    if (i > 0 && g[(i - 1) * m + j] == c) return 1;
    if (i + 1 < n && g[(i + 1) * m + j] == c) return 1;
    if (j + 1 < m && g[i * m + j + 1] == c) return 1;
    if (j > 0) {
        char left = left_override ? left_override : g[i * m + j - 1];
        if (left == c) return 1;
    } else if (left_override == c) {
        return 1;
    }
    return 0;
}

/* cell_colour: smallest legal letter for the empty cell (i,j). */
static char cell_colour(const char *g, int n, int m,
                        int i, int j, char left_override)
{
    for (char c = 'A'; c <= 'Z'; c++)
        if (!conflicts(g, n, m, i, j, c, left_override))
            return c;
    return 'Z';
}

/* can_place: may a square of side s coloured c start at (i,j)? */
static int can_place(const char *g, int n, int m,
                     int i, int j, int s, char c)
{
    if (i + s > n || j + s > m)
        return 0;
    for (int r = i; r < i + s; r++)
        for (int q = j; q < j + s; q++)
            if (g[r * m + q])
                return 0;
    for (int q = j; q < j + s; q++) {          /* rows above and below */
        if (i > 0 && g[(i - 1) * m + q] == c) return 0;
        if (i + s < n && g[(i + s) * m + q] == c) return 0;
    }
    for (int r = i; r < i + s; r++) {          /* columns left and right */
        if (j > 0 && g[r * m + j - 1] == c) return 0;
        if (j + s < m && g[r * m + j + s] == c) return 0;
    }
    return 1;
}

/* solver: paints the whole n x m table. */
static void solver(int n, int m, char *g)
/*@ Require
      1 <= n && n <= 100 && 1 <= m && m <= 100 && CharArray::full_shape(g, n * m)
    Ensure
      exists (out : list(list Z)), Spec(n, m, out) &&
        CharArray::full(g, n * m, concat(out))
*/
{
    for (int i = 0; i < n; i++)
        for (int j = 0; j < m; j++)
            g[i * m + j] = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < m; j++) {
            if (g[i * m + j])
                continue;
            char c = 0;
            for (char t = 'A'; t <= 'Z'; t++)
                if (can_place(g, n, m, i, j, 1, t)) {
                    c = t;
                    break;
                }
            int size = 1;
            while (j + size < m && can_place(g, n, m, i, j, size + 1, c)) {
                /* would the next cell of this row settle for something worse? */
                if (cell_colour(g, n, m, i, j + size, c) > c)
                    size++;
                else
                    break;
            }
            for (int r = i; r < i + size; r++)
                for (int q = j; q < j + size; q++)
                    g[r * m + q] = c;
        }
}

// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     char *g = malloc(sizeof(char) * (size_t)n * m);
//     solver(n, m, g);
//     for (int i = 0; i < n; i++) {
//         for (int j = 0; j < m; j++)
//             putchar(g[i * m + j]);
//         putchar('\n');
//     }
//     return 0;
// }
