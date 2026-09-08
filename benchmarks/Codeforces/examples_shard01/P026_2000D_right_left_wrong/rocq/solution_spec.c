/*
 * Codeforces 2000/D - Right Left Wrong  (rating 1200, GREEDY)
 *
 * All a_i are positive, so a segment is worth taking whenever it exists.
 * Pairing the outermost 'L' with the outermost 'R', then the next pair inside,
 * and so on, covers the largest possible total: nested pairs never conflict
 * and any crossing pairing covers no more cells.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : list Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P026_2000D_right_left_wrong.rocq.spec_lib */

/* solver: pure.  Maximum score for strip a[0..n-1] with letters s[0..n-1]. */
static long long solver(const int *a, const char *s, int n, long long *pre)
/*@ With (values : list Z) (directions : list Z)
    Require
      2 <= n && n <= 200000 &&
      (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 100000)) &&
      (forall i, (0 <= i && i < n) => (directions[i] == 76 || directions[i] == 82)) &&
      n == Zlength(values) && Zlength(directions) == n && IntArray::full(a, n, values) * CharArray::full(s, n, directions) * Int64Array::undef_full(pre, n + 1)
    Ensure
      Spec(values, directions, __return) &&
      IntArray::full(a, n, values) * CharArray::full(s, n, directions) * Int64Array::full_shape(pre, n + 1)
*/
{
    pre[0] = 0;
    for (int i = 0; i < n; i++)
        pre[i + 1] = pre[i] + a[i];

    long long score = 0;
    int l = 0, r = n - 1;
    while (l < r) {
        while (l < r && s[l] != 'L')
            l++;
        while (l < r && s[r] != 'R')
            r--;
        if (l < r) {
            score += pre[r + 1] - pre[l];
            l++;
            r--;
        }
    }
    return score;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[200005];
//     static char s[200005];
//     static long long pre[200006];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         scanf("%200004s", s);
//         printf("%lld\n", solver(a, s, n, pre));
//     }
//     return 0;
// }
