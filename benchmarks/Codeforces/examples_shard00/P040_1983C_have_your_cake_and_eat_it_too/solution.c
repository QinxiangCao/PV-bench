/* Codeforces 1983/C - Have Your Cake and Eat It Too */
#include <stdio.h>
#include <stdlib.h>

static int try_order(long long **v, int n, long long need, const int order[3], int out[6])
{
    int left[3], right[3], pos = 0;
    for (int part = 0; part < 2; ++part) {
        int who = order[part], start = pos; long long sum = 0;
        while (pos < n && sum < need) sum += v[who][pos++];
        if (sum < need) return 0;
        left[who] = start + 1; right[who] = pos;
    }
    int who = order[2]; long long sum = 0;
    for (int i = pos; i < n; ++i) sum += v[who][i];
    if (sum < need) return 0;
    left[who] = pos + 1; right[who] = n;
    for (int i = 0; i < 3; ++i) { out[2 * i] = left[i]; out[2 * i + 1] = right[i]; }
    return 1;
}

static int solver(long long **v, int n, int out[6])
{
    static const int orders[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
    long long total = 0; for (int i = 0; i < n; ++i) total += v[0][i];
    long long need = (total + 2) / 3;
    for (int z = 0; z < 6; ++z) if (try_order(v, n, need, orders[z], out)) return 1;
    return 0;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; scanf("%d", &n);
        long long *v[3]; int out[6];
        for (int p = 0; p < 3; ++p) {
            v[p] = malloc((size_t)n * sizeof(**v));
            for (int i = 0; i < n; ++i) scanf("%lld", &v[p][i]);
        }
        int ok = solver(v, n, out);
        if (!ok) puts("-1");
        else printf("%d %d %d %d %d %d\n", out[0], out[1], out[2], out[3], out[4], out[5]);
        for (int p = 0; p < 3; ++p) free(v[p]);
    }
    return 0;
}
