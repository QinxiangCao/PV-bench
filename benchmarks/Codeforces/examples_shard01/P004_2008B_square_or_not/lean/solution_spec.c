/*@ Import Lean
import Codeforces.examples_shard01.P004_2008B_square_or_not.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 2008/B - Square or Not  (rating 800, STRINGS)
 *
 * The matrix is square iff n is a perfect square r*r and the string, read as
 * an r x r grid, is 1 exactly on the border and 0 strictly inside.
 */

// #include <stdio.h>
/*@ Extern Coq
        (Pre : list Z -> Prop)
        (Spec : list Z -> Z -> Prop)
*/
/* solver: pure.  1 if s (length n) can come from a square beautiful matrix. */
static int solver(const char *s, int n)
/*@ With (bits : list Z)
    Require
      2 <= n && n <= 200000 &&
      Zlength(bits) == n &&
      (forall i, (0 <= i && i < n) =>
        (bits[i] == 48 || bits[i] == 49)) &&
      Pre(bits) &&
      CharArray::full(s, n, bits)
    Ensure
      Spec(bits, __return) &&
      CharArray::full(s, n, bits)
*/
{
    int r = 0;
    while ((r + 1) * (r + 1) <= n)
        r++;
    if (r * r != n)
        return 0;
    for (int i = 0; i < r; i++)
        for (int j = 0; j < r; j++) {
            int border = (i == 0 || i == r - 1 || j == 0 || j == r - 1);
            char want = border ? '1' : '0';
            if (s[i * r + j] != want)
                return 0;
        }
    return 1;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n;
//         static char s[200005];
//         scanf("%d %200004s", &n, s);
//         puts(solver(s, n) ? "Yes" : "No");
//     }
//     return 0;
// }
