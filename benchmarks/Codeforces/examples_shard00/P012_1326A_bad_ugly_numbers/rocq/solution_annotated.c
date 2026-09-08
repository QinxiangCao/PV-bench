/* Codeforces 1326/A - Bad Ugly Numbers */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> option (list Z) -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.rocq.spec_lib */

static int solver(int n, char *out)

/*@
    Require
      1 <= n && n <= 100000 &&
      CharArray::undef_full(out, 100001)
    Ensure
      ((__return == -1 && Spec(n, None) && CharArray::undef_full(out, 100001)) ||
       (exists digits chars,
          Spec(n, Some(digits)) &&
          Zlength(chars) == Zlength(digits) &&
          (forall i, (0 <= i && i < Zlength(digits)) => chars[i] == digits[i] + 48) &&
          __return == Zlength(digits) &&
          CharArray::full(out, Zlength(chars) + 1, app(chars, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(chars) + 1, 100001)))
*/

{
    if (n == 1) return -1;
    out[0] = '2';
    /*@ Inv Assert
      exists (chars : list Z),
        n == n@pre && out == out@pre &&
        2 <= n@pre && n@pre <= 100000 &&
        1 <= i && i <= n@pre &&
        Zlength(chars) == i &&
        chars[0] == 50 &&
        (forall (k : Z),
          (1 <= k && k < i) => chars[k] == 51) &&
        CharArray::seg(out, 0, i, chars) *
        CharArray::undef_seg(out, i, 100001)
    */
    for (int i = 1; i < n; ++i) out[i] = '3';
    out[n] = '\0';
    return n;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; static char out[100001]; scanf("%d", &n);
//         if (solver(n, out) < 0) puts("-1"); else puts(out);
//     }
//     return 0;
// }
