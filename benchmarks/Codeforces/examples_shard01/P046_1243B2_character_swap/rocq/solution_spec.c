/*
 * Codeforces 1243/B2 - Character Swap (Hard Version)  (rating 1600, STRINGS)
 *
 * Solvable iff every letter occurs an even number of times overall.  Fix
 * positions left to right: to repair position i, find another copy of s[i]
 * further right — in s[j], which takes one swap (s_j <-> t_i), or in t[j],
 * which first needs s_j <-> t_j to move it into s.  That is at most 2 swaps
 * per position, so at most 2n in total.
 */

// #include <stdio.h>
// #include <string.h>
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P046_1243B2_character_swap.rocq.spec_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> option(list(Z*Z)) -> Prop)
*/


/* solver: pure.  Fills oi/oj with the swap pairs (1-based) and returns the
 * number of swaps, or -1 if the strings cannot be made equal.  s and t are
 * modified into their final (equal) state. */
static int solver(char *s, char *t, int n, int *oi, int *oj)
/*@ With (source : list Z) (target : list Z)
    Require
      Pre(source, target) &&
      2 <= n && n <= 50 && (forall i, (0 <= i && i < n) => (97 <= source[i] && source[i] <= 122)) && (forall i, (0 <= i && i < n) => (97 <= target[i] && target[i] <= 122)) &&
      n == Zlength(source) && Zlength(target) == n && CharArray::full(s, n, source) * CharArray::full(t, n, target) * IntArray::undef_full(oi, 2 * n) * IntArray::undef_full(oj, 2 * n)
    Ensure
      exists (out : option(list(Z*Z))),
        Spec(source, target, out) &&
        ((out == None && __return == -1 && exists (oi_cells : list(option Z)) (oj_cells : list(option Z)), CharArray::full_shape(s, n) * CharArray::full_shape(t, n) * IntArray::mixed_full(oi, 2 * n, oi_cells) * IntArray::mixed_full(oj, 2 * n, oj_cells)) || (exists (ops : list(Z*Z)), out == Some(ops) && __return == Zlength(ops) && 1 <= Zlength(ops) && Zlength(ops) <= 2 * n && exists (is : list Z) (js : list Z), Zlength(is) == Zlength(ops) && Zlength(js) == Zlength(ops) && (forall q, (0 <= q && q < Zlength(ops)) => is[q] == fst(ops[q]) + 1 && js[q] == snd(ops[q]) + 1) && CharArray::full_shape(s, n) * CharArray::full_shape(t, n) * IntArray::full(oi, Zlength(ops), is) * IntArray::undef_seg(oi, Zlength(ops), 2 * n) * IntArray::full(oj, Zlength(ops), js) * IntArray::undef_seg(oj, Zlength(ops), 2 * n)))
*/
{
    int cnt[26] = {0};
    for (int i = 0; i < n; i++) {
        cnt[s[i] - 'a']++;
        cnt[t[i] - 'a']++;
    }
    for (int c = 0; c < 26; c++)
        if (cnt[c] % 2) {
            return -1;
        }

    int m = 0;
    for (int i = 0; i < n; i++) {
        if (s[i] == t[i])
            continue;
        int j;
        for (j = i + 1; j < n; j++)
            if (s[j] == s[i])
                break;
        if (j < n) {                       /* one swap: s_j <-> t_i */
            char tmp = s[j];
            s[j] = t[i];
            t[i] = tmp;
            oi[m] = j + 1;
            oj[m] = i + 1;
            m++;
            continue;
        }
        for (j = i + 1; j < n; j++)
            if (t[j] == s[i])
                break;
        if (j >= n)
            return -1;                     /* cannot happen: counts are even */
        char tmp = s[j];                   /* move it into s: s_j <-> t_j */
        s[j] = t[j];
        t[j] = tmp;
        oi[m] = j + 1;
        oj[m] = j + 1;
        m++;
        tmp = s[j];                        /* then s_j <-> t_i */
        s[j] = t[i];
        t[i] = tmp;
        oi[m] = j + 1;
        oj[m] = i + 1;
        m++;
    }
    return m;
}

// int main(void)
// {
//     int k;
//     if (scanf("%d", &k) != 1)
//         return 0;
//     static char s[55], t[55];
//     static int oi[205], oj[205];
//     while (k--) {
//         int n;
//         scanf("%d %54s %54s", &n, s, t);
//         int m = solver(s, t, n, oi, oj);
//         if (m < 0) {
//             puts("No");
//             continue;
//         }
//         puts("Yes");
//         printf("%d\n", m);
//         for (int i = 0; i < m; i++)
//             printf("%d %d\n", oi[i], oj[i]);
//     }
//     return 0;
// }
