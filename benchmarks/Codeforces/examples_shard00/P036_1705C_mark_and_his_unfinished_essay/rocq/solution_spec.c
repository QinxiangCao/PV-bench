/* Codeforces 1705/C - Mark and His Unfinished Essay */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : list Z -> list (Z * Z) -> list Z -> Prop)
      (Spec : list Z -> list (Z * Z) -> list Z -> list Z -> Prop)
      (store_string : Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P036_1705C_mark_and_his_unfinished_essay.rocq.spec_lib */

static void
solver(const char *s, int c, const long long *l, const long long *r, int q,
       const long long *queries,
       char *answers) 

/*@ With (text : list Z)
             (ops : list (Z * Z))
             (queries_data : list Z)
             (lefts rights : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 200000 &&
      1 <= Zlength(ops) && Zlength(ops) <= 40 &&
      1 <= Zlength(queries_data) && Zlength(queries_data) <= 10000 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      Pre(text, ops, queries_data) &&
      c == Zlength(ops) && q == Zlength(queries_data) &&
      Zlength(lefts) == c && Zlength(rights) == c &&
      (forall i, (0 <= i && i < c) =>
        (fst(ops[i]) == lefts[i] &&
         snd(ops[i]) == rights[i])) &&
      store_string(s, text) *
      Int64Array::full(l, c, lefts) *
      Int64Array::full(r, c, rights) *
      Int64Array::full(queries, q, queries_data) *
      CharArray::undef_full(answers, q)
    Ensure
      exists out,
        Spec(text, ops, queries_data, out) &&
        store_string(s, text) *
        Int64Array::full(l, c, lefts) *
        Int64Array::full(r, c, rights) *
        Int64Array::full(queries, q, queries_data) *
        CharArray::full(answers, q, out)
*/

{
    long long before[40], length = (long long)strlen(s) ;
    
    for (int i = 0; i < c; ++i)
    {
        before[i] = length;
        length += r[i] - l[i] + 1;
    }
    
    for (int z = 0; z < q; ++z)
    {
        long long k = queries[z];
        
        for (int i = c - 1; i >= 0; --i)
            if (k > before[i])
                k = l[i] + k - before[i] - 1;
        
        answers[z] = s[k - 1];
    }
    
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, c, q; scanf("%d %d %d", &n, &c, &q);
//         char *s = malloc((size_t)n + 1); scanf("%s", s);
//         long long l[40], r[40];
//         for (int i = 0; i < c; ++i) {
//             scanf("%lld %lld", &l[i], &r[i]);
//         }
//         long long *queries = malloc((size_t)q * sizeof(*queries)); char *answers = malloc((size_t)q);
//         for (int i = 0; i < q; ++i) scanf("%lld", &queries[i]);
//         solver(s, c, l, r, q, queries, answers);
//         for (int i = 0; i < q; ++i) printf("%c\n", answers[i]);
//         free(answers); free(queries);
//         free(s);
//     }
//     return 0;
// }
