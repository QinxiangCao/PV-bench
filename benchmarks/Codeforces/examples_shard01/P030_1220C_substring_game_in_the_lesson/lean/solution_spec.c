/*@ Import Lean
import Codeforces.examples_shard01.P030_1220C_substring_game_in_the_lesson.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 1220/C - Substring Game in the Lesson  (rating 1300, GAMES)
 *
 * Extending to the left with a strictly smaller first letter always lowers the
 * substring, and extending to the right never does (it only appends).  So Ann
 * can move iff some letter before position k is smaller than s[k]; after such
 * a move the new first letter is the minimum available and Mike is stuck.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : list Z -> list Z -> Prop)
*/

/* solver: pure.  Fills win[i] with 1 if Ann wins for k = i, else 0. */
static void solver(const char *s, int n, char *win)
/*@ With (text : list Z)
    Require
      1 <= n && n <= 500000 &&
      (forall i, (0 <= i && i < n) => (97 <= text[i] && text[i] <= 122)) &&
      n == Zlength(text) && CharArray::full(s, n, text) * CharArray::undef_full(win, n)
    Ensure
      exists (out : list Z),
        Spec(text, out) &&
        CharArray::full(s, n, text) * CharArray::full(win, n, out)
*/
{
    char mn = 'z' + 1;
    for (int k = 0; k < n; k++) {
        win[k] = (mn < s[k]);
        if (s[k] < mn)
            mn = s[k];
    }
}

// int main(void)
// {
//     static char s[500005], win[500005];
//     if (scanf("%500004s", s) != 1)
//         return 0;
//     int n = 0;
//     while (s[n])
//         n++;
//     solver(s, n, win);
//     for (int i = 0; i < n; i++)
//         puts(win[i] ? "Ann" : "Mike");
//     return 0;
// }
