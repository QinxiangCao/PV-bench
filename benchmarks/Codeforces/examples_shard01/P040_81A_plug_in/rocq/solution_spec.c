/*
 * Codeforces 81/A - Plug-in  (rating 1400, IMPLEMENTATION)
 *
 * Push characters on a stack; whenever the incoming character equals the top,
 * pop instead, which cancels the pair and immediately exposes any pair that
 * the deletion has created.
 */

// #include <stdio.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P040_81A_plug_in.rocq.spec_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Prop)
*/

/* solver: pure.  Reduces s[0..n-1] into out (NUL-terminated), returning its
 * length. */
static int solver(const char *s, int n, char *out)
/*@ With (text : list Z)
    Require
      1 <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (97 <= text[i] && text[i] <= 122)) &&
      n == Zlength(text) && CharArray::full(s, n, text) * CharArray::undef_full(out, n + 1)
    Ensure
      exists (out_spec : list Z),
        Spec(text, out_spec) &&
        __return == Zlength(out_spec) && CharArray::full(s, n, text) * CharArray::full(out, Zlength(out_spec) + 1, app(out_spec, cons(0, nil))) * CharArray::undef_seg(out, Zlength(out_spec) + 1, n + 1)
*/
{
    int top = 0;
    for (int i = 0; i < n; i++) {
        if (top > 0 && out[top - 1] == s[i])
            top--;
        else
            { out[top] = s[i]; top++; }
    }
    out[top] = '\0';
    return top;
}

// int main(void)
// {
//     static char s[200005], out[200005];
//     if (scanf("%200004s", s) != 1)
//         return 0;
//     int n = 0;
//     while (s[n])
//         n++;
//     solver(s, n, out);
//     puts(out);
//     return 0;
// }
