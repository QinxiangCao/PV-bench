/* Codeforces 887/A - Div. 64 */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/

/*@ Extern Coq
      (PrefixScan : list Z -> Z -> Z -> Prop)
*/
static int solver(const char *s)
/*@ With (text : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 100 &&
      (forall i, (0 <= i && i < Zlength(text)) =>
        (text[i] == 48 || text[i] == 49)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
*/

{
    int seen_one = 0, zeros = 0;
    
    for (int i = 0; s[i]; ++i) {
        if (s[i] == '1') seen_one = 1;
        else if (seen_one) ++zeros;
    }
    return zeros >= 6;
}

// int main(void)
// {
//     char s[105];
//     if (scanf("%104s", s) != 1) return 0;
//     puts(solver(s) ? "yes" : "no");
//     return 0;
// }
