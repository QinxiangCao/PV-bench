/*
 * Codeforces 1365/C - Rotation Matching  (rating 1400, GREEDY)
 *
 * Only the relative rotation matters.  Value v contributes a match exactly
 * when the shift equals (pos_a[v] - pos_b[v]) mod n, so tally that shift for
 * every value and take the most popular one.
 */

// #include <stdio.h>
// #include <string.h>
/*@ Extern Coq
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P038_1365C_rotation_matching.rocq.spec_lib */

static void *memset(void *dst, int c, unsigned long n)
/*@ Require
      0 <= n && c == 0 &&
      UCharArray::undef_full(dst, n)
    Ensure
      __return == dst &&
      UCharArray::full(dst, n, repeat_Z(0, n))
*/;


/* solver: pure.  Maximum matches over all cyclic shifts; pa/pb are the
 * position tables of the two permutations and cnt is scratch of size n. */
static int solver(const int *pa, const int *pb, int n, int *cnt)
/*@ With (a : list Z) (b : list Z)
    Require
      Pre(a, b) && 1 <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (1 <= a[i] && a[i] <= n)) && (forall i, (0 <= i && i < n) => (1 <= b[i] && b[i] <= n)) &&
      n == Zlength(a) && Zlength(b) == n && exists (pa_spec : list Z) (pb_spec : list Z), Zlength(pa_spec) == n + 1 && Zlength(pb_spec) == n + 1 && (forall i, (0 <= i && i < n) => pa_spec[a[i]] == i && pb_spec[b[i]] == i) && IntArray::full(pa, n + 1, pa_spec) * IntArray::full(pb, n + 1, pb_spec) * IntArray::undef_full(cnt, n)
    Ensure
      Spec(a, b, __return) &&
      exists (pa_spec : list Z) (pb_spec : list Z), Zlength(pa_spec) == n + 1 && Zlength(pb_spec) == n + 1 && (forall i, (0 <= i && i < n) => pa_spec[a[i]] == i && pb_spec[b[i]] == i) && IntArray::full(pa, n + 1, pa_spec) * IntArray::full(pb, n + 1, pb_spec) * IntArray::full_shape(cnt, n)
*/
{
    memset(cnt, 0, sizeof(int) * n);
    for (int v = 1; v <= n; v++) {
        int shift = pa[v] - pb[v];
        if (shift < 0)
            shift += n;
        cnt[shift] = cnt[shift] + 1;
    }
    int best = 0;
    for (int s = 0; s < n; s++)
        if (cnt[s] > best)
            best = cnt[s];
    return best;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int pa[200005], pb[200005], cnt[200005];
//     for (int i = 0; i < n; i++) {
//         int v;
//         scanf("%d", &v);
//         pa[v] = i;
//     }
//     for (int i = 0; i < n; i++) {
//         int v;
//         scanf("%d", &v);
//         pb[v] = i;
//     }
//     printf("%d\n", solver(pa, pb, n, cnt));
//     return 0;
// }
