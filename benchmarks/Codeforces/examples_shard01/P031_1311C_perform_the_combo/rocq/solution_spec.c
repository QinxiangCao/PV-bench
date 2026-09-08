/*
 * Codeforces 1311/C - Perform the Combo  (rating 1300, BRUTE FORCE)
 *
 * Position j (0-based) is pressed once per try that reaches past it: that is
 * the number of p_i > j, plus the final successful try.  A difference array
 * over the p values turns that into one linear pass.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P031_1311C_perform_the_combo.rocq.spec_lib */



static void *memset(void *dst, int c, unsigned long n)
{
    unsigned char *p = (unsigned char *)dst;
    for (unsigned long i = 0; i < n; i++)
        p[i] = (unsigned char)c;
    return dst;
}

static long long diff[200006];            /* work array, cleared on every call */

/* solver: reads no input.  cover[j] = number of tries pressing s[j]; accumulates
 * the per-letter totals into cnt[26]. */
static void solver(const char *s, int n, const int *p, int m, long long *cnt)
/*@ With (text : list Z) (tries : list Z)
    Require
      2 <= n && n <= 200000 && 1 <= m && m <= 200000 && (forall i, (0 <= i && i < n) => (97 <= text[i] && text[i] <= 122)) && (forall i, (0 <= i && i < m) => (1 <= tries[i] && tries[i] < n)) &&
      n == Zlength(text) && m == Zlength(tries) && CharArray::full(s, n, text) * IntArray::full(p, m, tries) * Int64Array::undef_full(cnt, 26) * Int64Array::undef_full(diff, n + 1)
    Ensure
      exists (out : list Z) (diff_after : list Z),
        Spec(text, tries, out) &&
        Zlength(diff_after) == n + 1 &&
        CharArray::full(s, n, text) * IntArray::full(p, m, tries) * Int64Array::full(cnt, 26, out) * Int64Array::full(diff, n + 1, diff_after)
*/
{
    memset(diff, 0, sizeof(long long) * (n + 1));   /* p_i may be n, so n + 1 */
    for (int i = 0; i < m; i++) {         /* try i presses s[0 .. p_i-1] */
        diff[0] = diff[0] + 1;
        diff[p[i]] = diff[p[i]] - 1;
    }
    diff[0] = diff[0] + 1;                /* the final, successful try */
    memset(cnt, 0, sizeof(long long) * 26);
    long long cover = 0;
    for (int j = 0; j < n; j++) {
        cover += diff[j];
        cnt[s[j] - 'a'] += cover;
    }
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static char s[200005];
//     static int p[200005];
//     long long cnt[26];
//     while (t--) {
//         int n, m;
//         scanf("%d %d", &n, &m);
//         scanf("%200004s", s);
//         for (int i = 0; i < m; i++)
//             scanf("%d", &p[i]);
//         solver(s, n, p, m, cnt);
//         for (int c = 0; c < 26; c++)
//             printf("%lld%c", cnt[c], c == 25 ? '\n' : ' ');
//     }
//     return 0;
// }
