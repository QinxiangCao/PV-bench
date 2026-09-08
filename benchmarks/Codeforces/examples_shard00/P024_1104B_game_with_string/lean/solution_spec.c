/*@ Import Lean
import Codeforces.examples_shard00.P024_1104B_game_with_string.lean.spec_lib
open scoped SimpleC
*/

/* Codeforces 1104/B - Game with string */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
static char stack[100005];

static int solver(const char *s)

/*@ With (text : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
      CharArray::undef_full(stack, 100005)
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
      CharArray::undef_full(stack, 100005)
*/

{
    int top = 0, moves = 0;

    for (int i = 0; s[i]; ++i)
    {
        if (top && stack[top - 1] == s[i])
        {
            --top;
            ++moves;
        }
        else
        {
            stack[top] = s[i];
            ++top;
        }
    }
    return moves & 1;
}

// int main(void)
// {
//     static char s[100005];
//     if (scanf("%100004s", s) != 1) return 0;
//     puts(solver(s) ? "Yes" : "No");
//     return 0;
// }
