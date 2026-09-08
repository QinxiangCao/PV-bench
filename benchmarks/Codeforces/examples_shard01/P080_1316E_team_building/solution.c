/*
 * Codeforces 1316/E - Team Building  (rating 2300, BITMASK DP)
 *
 * Sort people by audience strength descending and sweep.  With i people seen
 * and a set mask of positions already filled, exactly i - |mask| of them were
 * audience candidates, so the audience is always the strongest available
 * people: dp[i][mask] extends by making person i+1 audience (while a seat is
 * free), a player in any empty position, or by skipping them.
 */

#include <stdio.h>
#include <stdlib.h>

/* popcount: number of 1-bits in v.  Replaces the compiler builtin, which has no
 * body.  p <= 7, so v < 128 here. */
static int popcount(unsigned int v)
{
    int c = 0;
    while (v) {
        c = c + (int)(v & 1u);
        v >>= 1;
    }
    return c;
}

static void sift_people(long long *audience, int *order, int root, int hi)
{
    while (2 * root + 1 <= hi) {
        int child = 2 * root + 1;
        if (child + 1 <= hi && audience[child] < audience[child + 1])
            child++;
        if (audience[root] >= audience[child])
            return;
        long long t = audience[root]; audience[root] = audience[child];
        audience[child] = t;
        int q = order[root]; order[root] = order[child]; order[child] = q;
        root = child;
    }
}

static void sort_people(long long *audience, int *order, int n)
{
    for (int root = n / 2 - 1; root >= 0; root--)
    {
        sift_people(audience, order, root, n - 1);
    }
    for (int hi = n - 1; hi > 0; hi--) {
        long long t = audience[0]; audience[0] = audience[hi];
        audience[hi] = t;
        int q = order[0]; order[0] = order[hi]; order[hi] = q;
        sift_people(audience, order, 0, hi - 1);
    }
}

/* solver: maximum total strength.  s is row-major n x p. */
static long long solver(long long *audience, int *order,
                        const long long *s, int n, int p, int k,
                        long long *dp, long long *ndp)
{
    sort_people(audience, order, n);
    int full = 1 << p;
    for (int m = 0; m < full; m++)
        dp[m] = (-(1LL << 60));
    dp[0] = 0;
    for (int i = 0; i < n; i++) {
        for (int m = 0; m < full; m++)
            ndp[m] = (-(1LL << 60));
        int rank = n - 1 - i;             /* arrays are sorted ascending */
        int person = order[rank];
        for (int m = 0; m < full; m++) {
            if (dp[m] == (-(1LL << 60)))
                continue;
            int used = popcount((unsigned int)m);
            int aud = i - used;           /* audience members chosen so far */
            if (dp[m] > ndp[m])           /* skip this person */
                ndp[m] = dp[m];
            if (aud < k) {                /* seat them in the audience */
                long long v = dp[m] + audience[rank];
                if (v > ndp[m])
                    ndp[m] = v;
            }
            for (int j = 0; j < p; j++)
                if (!(m & (1 << j))) {
                    long long v = dp[m] + s[(long long)person * p + j];
                    int nm = m | (1 << j);
                    if (v > ndp[nm])
                        ndp[nm] = v;
                }
        }
        for (int m = 0; m < full; m++)
            dp[m] = ndp[m];
    }
    return dp[full - 1];
}

int main(void)
{
    int n, p, k;
    if (scanf("%d %d %d", &n, &p, &k) != 3)
        return 0;
    long long *audience = malloc(sizeof(long long) * n);
    int *order = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) {
        scanf("%lld", &audience[i]);
        order[i] = i;
    }
    long long *s = malloc(sizeof(long long) * (size_t)n * p);
    for (long long i = 0; i < (long long)n * p; i++)
        scanf("%lld", &s[i]);
    static long long dp[128], ndp[128];
    printf("%lld\n", solver(audience, order, s, n, p, k, dp, ndp));
    return 0;
}
