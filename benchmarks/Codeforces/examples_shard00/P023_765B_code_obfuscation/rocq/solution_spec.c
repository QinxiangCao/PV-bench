/* Codeforces 765/B - Code obfuscation */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P023_765B_code_obfuscation.rocq.spec_lib */

static int solver(const char *s)

/*@ With (text : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 500 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
*/

{
    char next = 'a';
    
    for (int i = 0; s[i]; ++i) {
        if (s[i] > next) return 0;
        if (s[i] == next && next < 'z') ++next;
    }
    return 1;
}

// int main(void)
// {
//     char s[505];
//     if (scanf("%504s", s) != 1) return 0;
//     puts(solver(s) ? "YES" : "NO");
//     return 0;
// }
