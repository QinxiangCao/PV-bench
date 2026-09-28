/* Codeforces 1729/F - Kirei and the Linear Function */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"
#include "array2_ext_def.h"

typedef unsigned long size_t;

void *calloc(size_t nmemb, size_t size)
/*@ Require
      0 <= nmemb && size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, nmemb, repeat_Z(0, nmemb))
*/;

void free(void *ptr)
/*@ Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/;

/*@ Extern Coq
      (Spec : Z -> list Z -> list (Z * Z * Z) -> list (Z * Z) -> Prop)
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
*/

/*@ Extern Coq
      (DigitPrefixSums : list Z -> list Z -> Z -> Prop)
      (pos_init_stage : Z -> list (list (option Z)))
      (PositionsPrefix : list Z -> Z -> Z -> list (list Z) -> Prop)
      (QueryBestPrefix : list Z -> Z -> (Z * Z * Z) -> Z -> Z -> Z -> Prop)
      (QueryOutputPrefix : Z -> list Z -> list (Z * Z * Z) -> Z -> list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (FlatPositionsPrefix : list Z -> Z -> Z -> list Z -> Prop)
*/
static void
solver(const char *s, int w, int m, const int *ql, const int *qr, const int *qk, int *out1,
       int *out2) 
/*@ With (text : list Z)
             (qs : list (Z * Z * Z))
             (ql_data qr_data qk_data : list Z)
    Require
      2 <= Zlength(text) && Zlength(text) <= 200000 &&
      1 <= w && w < Zlength(text) &&
      (forall i, (0 <= i && i < Zlength(text)) =>
        (48 <= text[i] && text[i] <= 57)) &&
      m == Zlength(qs) && Zlength(ql_data) == m &&
      Zlength(qr_data) == m && Zlength(qk_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (ql_data[i] == ztriple_1(qs[i]) && qr_data[i] == ztriple_2(qs[i]) &&
         qk_data[i] == ztriple_3(qs[i]) &&
         1 <= ql_data[i] && ql_data[i] <= qr_data[i] &&
         qr_data[i] <= Zlength(text) &&
         0 <= qk_data[i] && qk_data[i] < 9)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
      IntArray::full(ql, m, ql_data) * IntArray::full(qr, m, qr_data) *
      IntArray::full(qk, m, qk_data) *
      IntArray::undef_full(out1, m) * IntArray::undef_full(out2, m)
    Ensure
      exists out out1_data out2_data,
        Spec(w, text, qs, out) &&
        Zlength(out) == m && Zlength(out1_data) == m && Zlength(out2_data) == m &&
        (forall i, (0 <= i && i < m) =>
          (out1_data[i] == fst(out[i]) && out2_data[i] == snd(out[i]))) &&
        CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
        IntArray::full(ql, m, ql_data) * IntArray::full(qr, m, qr_data) *
        IntArray::full(qk, m, qk_data) *
        IntArray::full(out1, m, out1_data) * IntArray::full(out2, m, out2_data)
*/
{
    
    int n = (int)strlen(s),
        *pre = calloc((size_t)n + 1, sizeof(*pre));
    
    for (int i = 0; i < n; ++i)
        pre[i + 1] = pre[i] + s[i] - '0';
    int pos[18];
    
    for (int r = 0; r < 9; ++r)
    {
        pos[2 * r] = -1;
        pos[2 * r + 1] = -1;
    }
    
    for (int i = 0; i + w <= n; ++i)
    {
        int r = (pre[i + w] - pre[i]) % 9;
        
        if (pos[2 * r] < 0)
            pos[2 * r] = i + 1;
        else if (pos[2 * r + 1] < 0)
            pos[2 * r + 1] = i + 1;
    }
    
    for (int z = 0; z < m; ++z)
    {
        int l = ql[z], r = qr[z], k = qk[z], v = (pre[r] - pre[l - 1]) % 9, best1 = 1 << 30,
            best2 = 1 << 30;

        for (int a = 0; a < 9; ++a)
        {
            int b = (k - a * v) % 9;
            if (b < 0)
                b += 9;
            
            if (pos[2 * a] < 0)
                continue;
            int p1 = pos[2 * a], p2 = (a == b) ? pos[2 * b + 1] : pos[2 * b];
            if (p2 < 0)
                continue;
            if (p1 < best1 || (p1 == best1 && p2 < best2))
            {
                best1 = p1;
                best2 = p2;
            }
        }
        
        out1[z] = best1 == (1 << 30) ? -1 : best1;
        out2[z] = best1 == (1 << 30) ? -1 : best2;
    }
    
    free(pre);
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         char *s = malloc(200005);
//         scanf("%s", s);
//         int w, m;
//         scanf("%d %d", &w, &m);
//         int *l = malloc((size_t)m * sizeof(*l)), *r = malloc((size_t)m * sizeof(*r)),
//             *k = malloc((size_t)m * sizeof(*k)), *o1 = malloc((size_t)m * sizeof(*o1)),
//             *o2 = malloc((size_t)m * sizeof(*o2));
//         for (int i = 0; i < m; ++i)
//             scanf("%d %d %d", &l[i], &r[i], &k[i]);
//         solver(s, w, m, l, r, k, o1, o2);
//         for (int i = 0; i < m; ++i)
//             printf("%d %d\n", o1[i], o2[i]);
//         free(l);
//         free(r);
//         free(k);
//         free(o1);
//         free(o2);
//         free(s);
//     }
//     return 0;
// }
