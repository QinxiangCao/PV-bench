/*
 * Codeforces 1594/D - The Number of Imposters  (rating 1700, GRAPHS)
 *
 * "crewmate" forces the two players into the same role, "imposter" into
 * different ones, so each comment is a parity edge.  Two-colour every
 * component: contradictions mean -1, otherwise the component contributes the
 * larger of its two colour classes.
 */

#include <stdio.h>

#define MAXN 200005
#define MAXM 500005

/* solver: maximum number of imposters over n players, or -1 on contradiction. */
static long long solver(int n, int m,
                        const int *comment_u, const int *comment_v,
                        const int *comment_diff,
                        int *head, int *nxt, int *to, int *wt,
                        int *color, int *stack_)
{
    for (int v = 1; v <= n; v++)
        head[v] = -1;
    for (int i = 0; i < m; i++) {
        int e = 2 * i, u = comment_u[i], v = comment_v[i];
        to[e] = v; wt[e] = comment_diff[i]; nxt[e] = head[u]; head[u] = e;
        to[e + 1] = u; wt[e + 1] = comment_diff[i];
        nxt[e + 1] = head[v]; head[v] = e + 1;
    }
    for (int v = 1; v <= n; v++)
        color[v] = -1;
    long long total = 0;
    for (int s = 1; s <= n; s++) {
        if (color[s] >= 0)
            continue;
        int top = 0;
        color[s] = 0;
        { stack_[top] = s; top++; }
        int c0 = 0, c1 = 0;
        while (top) {
            top--;
            int u = stack_[top];
            if (color[u] == 0) c0++; else c1++;
            for (int e = head[u]; e != -1; e = nxt[e]) {
                int v = to[e], want = color[u] ^ wt[e];
                if (color[v] < 0) {
                    color[v] = want;
                    { stack_[top] = v; top++; }
                } else if (color[v] != want) {
                    return -1;
                }
            }
        }
        total += c0 > c1 ? c0 : c1;
    }
    return total;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    while (t--) {
        int n, m;
        scanf("%d %d", &n, &m);
        static int comment_u[MAXM], comment_v[MAXM], comment_diff[MAXM];
        static int head[MAXN], nxt[2 * MAXM], to[2 * MAXM], wt[2 * MAXM];
        static int color[MAXN], stack_[MAXN];
        for (int q = 0; q < m; q++) {
            int i, j;
            char c[16];
            scanf("%d %d %15s", &i, &j, c);
            comment_u[q] = i;
            comment_v[q] = j;
            comment_diff[q] = (c[0] == 'i'); /* imposter: different roles */
        }
        printf("%lld\n", solver(n, m, comment_u, comment_v, comment_diff,
                                head, nxt, to, wt, color, stack_));
    }
    return 0;
}
