/*
 * Codeforces 1569/D - Inconvenient Pairs  (rating 1900, SORTINGS)
 *
 * A person standing on a crossing is never inconvenient.  Otherwise the person
 * is stuck strictly between two parallel streets: two people trapped in the
 * same horizontal strip must detour unless they share the same x (and
 * symmetrically for vertical strips).  So per strip count all pairs and
 * subtract the pairs sharing a coordinate.
 */

#include <stdio.h>

/* strip: index of the gap of the sorted street list that v falls into, or -1
 * if v is exactly on a street. */
static int strip(const int *s, int n, int v)
{
    int lo = 0, hi = n - 1;
    while (lo < hi) {                     /* last street <= v */
        int mid = lo + (hi - lo + 1) / 2;
        if (s[mid] <= v)
            lo = mid;
        else
            hi = mid - 1;
    }
    return s[lo] == v ? -1 : lo;
}

static int item_less(int grp1, int key1, int grp2, int key2)
{
    return grp1 < grp2 || (grp1 == grp2 && key1 < key2);
}

static void sift_items(int *grp, int *key, int root, int upper)
{
    while (2 * root + 1 <= upper) {
        int child = 2 * root + 1;
        if (child + 1 <= upper &&
            item_less(grp[child], key[child], grp[child + 1], key[child + 1]))
            child++;
        if (!item_less(grp[root], key[root], grp[child], key[child]))
            return;
        int t = grp[root]; grp[root] = grp[child]; grp[child] = t;
        t = key[root]; key[root] = key[child]; key[child] = t;
        root = child;
    }
}

static void sort_items(int *grp, int *key, int cnt)
{
    for (int root = cnt / 2 - 1; root >= 0; root--)
        sift_items(grp, key, root, cnt - 1);
    for (int upper = cnt - 1; upper > 0; upper--) {
        int t = grp[0]; grp[0] = grp[upper]; grp[upper] = t;
        t = key[0]; key[0] = key[upper]; key[upper] = t;
        sift_items(grp, key, 0, upper - 1);
    }
}

/* count_pairs: pairs inside each group that differ in key. */
static long long count_pairs(int *grp, int *key, int cnt)
{
    sort_items(grp, key, cnt);
    long long total = 0;
    int i = 0;
    while (i < cnt) {
        int j = i;
        while (j < cnt && grp[j] == grp[i])
            j++;
        long long g = j - i;
        total += g * (g - 1) / 2;
        int p = i;
        while (p < j) {                   /* remove same-key pairs */
            int q = p;
            while (q < j && key[q] == key[p])
                q++;
            long long same = q - p;
            total -= same * (same - 1) / 2;
            p = q;
        }
        i = j;
    }
    return total;
}

/* solver: number of inconvenient pairs. */
static long long solver(const int *xs, int n, const int *ys, int m,
                        const int *px, const int *py, int k,
                        int *va_grp, int *va_key,
                        int *ha_grp, int *ha_key)
{
    int nv = 0, nh = 0;
    for (int p = 0; p < k; p++) {
        int sy = strip(ys, m, py[p]);
        int sx = strip(xs, n, px[p]);
        if (sy >= 0) {                    /* on a vertical street only */
            va_grp[nv] = sy;
            va_key[nv] = px[p];
            nv++;
        } else if (sx >= 0) {             /* on a horizontal street only */
            ha_grp[nh] = sx;
            ha_key[nh] = py[p];
            nh++;
        }
    }
    return count_pairs(va_grp, va_key, nv) +
           count_pairs(ha_grp, ha_key, nh);
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static int xs[200005], ys[200005], px[300005], py[300005];
    static int va_grp[300005], va_key[300005];
    static int ha_grp[300005], ha_key[300005];
    while (t--) {
        int n, m, k;
        scanf("%d %d %d", &n, &m, &k);
        for (int i = 0; i < n; i++)
            scanf("%d", &xs[i]);
        for (int i = 0; i < m; i++)
            scanf("%d", &ys[i]);
        for (int p = 0; p < k; p++)
            scanf("%d %d", &px[p], &py[p]);
        printf("%lld\n", solver(xs, n, ys, m, px, py, k,
                                va_grp, va_key, ha_grp, ha_key));
    }
    return 0;
}
