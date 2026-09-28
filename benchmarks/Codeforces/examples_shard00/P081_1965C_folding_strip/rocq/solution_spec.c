/* Codeforces 1965/C - Folding Strip */
// #include <stdio.h>
// #include <stdlib.h>
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Extern Coq
      (SpecEdges : list Z -> Z -> Prop)
      (FoldPrefixState : list Z -> Z -> Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (SpecAlternatingEdges : list Z -> Z -> Prop)
      (FoldPrefixAlternatingState : list Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int solver(int n, const char *s) 
/*@ With (text : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(text)) => ((text[i] == 48) || (text[i] == 49))) &&
      n == Zlength(text) &&
      CharArray::full(s, n + 1, app(text, cons(0, nil)))
    Ensure
      SpecAlternatingEdges(text, __return) &&
      CharArray::full(s, n + 1, app(text, cons(0, nil)))
*/
{
    int cur = 0, mn = 0, mx = 0;
    
    for (int i = 0; i < n; ++i)
    {
        if (((cur & 1) == 0) == (s[i] == '1'))
            ++cur;
        else
            --cur;
        if (cur < mn)
            mn = cur;
        if (cur > mx)
            mx = cur;
    }
    return mx - mn;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n;
//         char *s;
//         scanf("%d", &n);
//         s = malloc((size_t)n + 1);
//         scanf("%s", s);
//         printf("%d\n", solver(n, s));
//         free(s);
//     }
//     return 0;
// }
