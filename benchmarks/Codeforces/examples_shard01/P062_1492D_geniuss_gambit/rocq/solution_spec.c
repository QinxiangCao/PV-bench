/*
 * Codeforces 1492/D - Genius's Gambit  (rating 1900, CONSTRUCTIVE)
 *
 * Start from x = 1^b 0^a and build y by moving a single one from position i
 * into a zero at position j > i.  Then x - y = 2^(n-1-i) - 2^(n-1-j), whose
 * binary form is exactly j-i ones.  Avoiding a leading zero forces i >= 1, so
 * k can reach a+b-2 but no further, and a zero and at least two ones are
 * needed for any k >= 1.
 */

// #include <stdio.h>
// #include <string.h>
#include "string.h"

/* solver: pure.  Writes x and y (length a+b, NUL-terminated) and returns 1,
 * or returns 0 when no pair exists. */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P062_1492D_geniuss_gambit.rocq.spec_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> option(list Z * list Z) -> Prop)
      (pair : {A B} -> A -> B -> A * B)
*/
static int solver(int a, int b, int k, char *x, char *y)
/*@ Require
      0 <= a && 1 <= b && 0 <= k && k <= a + b && a + b <= 200000 &&
      CharArray::undef_full(x, a + b + 1) * CharArray::undef_full(y, a + b + 1)
    Ensure
      exists (out : option(list Z * list Z)),
        Spec(a@pre, b@pre, k@pre, out) &&
        ((out == None && __return == 0 &&
        CharArray::full_shape(x, a + b + 1) * CharArray::full_shape(y, a + b + 1)) || 
        (exists (xs : list Z) (ys : list Z), 
        out == Some(pair(xs, ys)) && __return == 1 && Zlength(xs) == a + b && Zlength(ys) == a + b && 
        exists (xbytes : list Z) (ybytes : list Z), Zlength(xbytes) == a + b && Zlength(ybytes) == a + b && 
        (forall i, (0 <= i && i < a + b) => xbytes[i] == xs[i] + 48 && ybytes[i] == ys[i] + 48) && 
        CharArray::full(x, a + b + 1, app(xbytes, cons(0, nil))) * CharArray::full(y, a + b + 1, app(ybytes, cons(0, nil)))))
*/
{
    int n = a + b;
    for (int i = 0; i < b; i++)
        x[i] = '1';
    for (int i = b; i < n; i++)
        x[i] = '0';
    x[n] = '\0';
    memcpy(y, x, n + 1);
    if (k == 0)
        return 1;
    if (a == 0 || b < 2 || k > n - 2)
        return 0;
    int i, j;
    if (k <= a) {
        i = b - 1;                        /* last one, into the zero field */
        j = i + k;
    } else {
        j = n - 1;                        /* last zero, from an earlier one */
        i = j - k;
    }
    y[i] = '0';
    y[j] = '1';
    return 1;
}

// int main(void)
// {
//     int a, b, k;
//     if (scanf("%d %d %d", &a, &b, &k) != 3)
//         return 0;
//     static char x[200005], y[200005];
//     if (solver(a, b, k, x, y)) {
//         puts("Yes");
//         puts(x);
//         puts(y);
//     } else {
//         puts("No");
//     }
//     return 0;
// }
