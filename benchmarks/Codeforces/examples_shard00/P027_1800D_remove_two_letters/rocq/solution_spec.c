/* Codeforces 1800/D - Remove Two Letters */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P027_1800D_remove_two_letters.rocq.spec_lib */

static int solver(const char *s, int n)

/*@ With (text : list Z)
    Require
      3 <= Zlength(text) && Zlength(text) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      n == Zlength(text) &&
      CharArray::full(s, n + 1, app(text, cons(0, nil)))
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, n + 1, app(text, cons(0, nil)))
*/

{
    int answer = n - 1;
    
    for (int i = 0; i + 2 < n; ++i) if (s[i] == s[i + 2]) --answer;
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; char s[200005]; scanf("%d %200004s", &n, s);
//         printf("%d\n", solver(s, n));
//     }
//     return 0;
// }
