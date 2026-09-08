/*
 * Codeforces 1365/C - Rotation Matching  (rating 1400, GREEDY)
 *
 * Only the relative rotation matters.  Value v contributes a match exactly
 * when the shift equals (pos_a[v] - pos_b[v]) mod n, so tally that shift for
 * every value and take the most popular one.
 */

#include <stdio.h>
#include <string.h>

/* solver: pure.  Maximum matches over all cyclic shifts; pa/pb are the
 * position tables of the two permutations and cnt is scratch of size n. */
static int solver(const int *pa, const int *pb, int n, int *cnt)
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

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static int pa[200005], pb[200005], cnt[200005];
    for (int i = 0; i < n; i++) {
        int v;
        scanf("%d", &v);
        pa[v] = i;
    }
    for (int i = 0; i < n; i++) {
        int v;
        scanf("%d", &v);
        pb[v] = i;
    }
    printf("%d\n", solver(pa, pb, n, cnt));
    return 0;
}
