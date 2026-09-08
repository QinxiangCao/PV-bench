/*
 * Codeforces 288/A - Polo the Penguin and Strings  (rating 1300, GREEDY)
 *
 * To stay smallest, use "abab..." as long as possible and park the remaining
 * k-2 distinct letters at the very end as "cde...".  That needs n - (k-2) >= 2
 * cells for the alternating part, which holds whenever k <= n; k = 1 works
 * only for n = 1.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> option(list Z) -> Prop)
      (P035ReturnBridge : option(list Z) -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P035_288A_polo_the_penguin_and_strings.rocq.spec_lib */

/* solver: pure.  Writes the answer into out (NUL-terminated) and returns 1,
 * or returns 0 when no such string exists. */
static int solver(int n, int k, char *out)
/*@ With (length : Z) (alphabet_size : Z)
    Require
      1 <= length && length <= 1000000 &&
      1 <= alphabet_size && alphabet_size <= 26 &&
      n == length && k == alphabet_size && CharArray::undef_full(out, n + 1)
    Ensure
      exists (out_spec : option(list Z)),
        Spec(length, alphabet_size, out_spec) &&
        P035ReturnBridge(out_spec, __return) &&
        n == length && k == alphabet_size && ((out_spec == None && __return == 0 && CharArray::undef_full(out, n + 1)) || (exists (xs : list Z), out_spec == Some(xs) && __return == 1 && Zlength(xs) == n && CharArray::full(out, n + 1, app(xs, cons(0, nil)))))
*/
{
    if (k > n || (k == 1 && n > 1))
        return 0;
    if (k == 1) {
        out[0] = 'a';
        out[1] = '\0';
        return 1;
    }
    int alt = n - (k - 2);                /* length of the "abab..." part */
    for (int i = 0; i < alt; i++)
        out[i] = 'a' + (i % 2);
    for (int i = 0; i < k - 2; i++)
        out[alt + i] = 'c' + i;
    out[n] = '\0';
    return 1;
}

// int main(void)
// {
//     int n, k;
//     if (scanf("%d %d", &n, &k) != 2)
//         return 0;
//     static char out[1000006];
//     if (solver(n, k, out))
//         puts(out);
//     else
//         puts("-1");
//     return 0;
// }
