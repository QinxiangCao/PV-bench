/* Codeforces 1537/B - Bad Boy */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Z * Z -> Z * Z -> Z * Z -> Prop)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P008_1537B_bad_boy.rocq.spec_lib */

static void solver(long long n, long long m, long long i, long long j,
                   long long out[4]) 

/*@ With (start : Z * Z)
    Require
      1 <= n && n <= 1000000000 &&
      1 <= m && m <= 1000000000 &&
      i == fst(start) && j == snd(start) &&
      1 <= i && i <= n && 1 <= j && j <= m &&
      Int64Array::undef_full(out, 4)
    Ensure
      exists p q,
        Spec(n, m, start, p, q) &&
        Int64Array::full(out, 4,
          cons(fst(p), cons(snd(p),
            cons(fst(q), cons(snd(q), nil)))))
*/

{
    (void)i;
    (void)j;
    out[0] = 1;
    out[1] = 1;
    out[2] = n;
    out[3] = m;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         long long n, m, i, j;
//         scanf("%lld %lld %lld %lld", &n, &m, &i, &j);
//         long long out[4]; solver(n, m, i, j, out);
//         printf("%lld %lld %lld %lld\n", out[0], out[1], out[2], out[3]);
//     }
//     return 0;
// }
