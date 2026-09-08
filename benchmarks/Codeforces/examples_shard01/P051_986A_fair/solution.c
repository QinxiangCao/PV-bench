/*
 * Codeforces 986/A - Fair  (rating 1600, BFS)
 *
 * Roads are unweighted, so one multi-source BFS per goods type gives, for every
 * town, the distance to the nearest town producing that type (k <= 100 BFS
 * runs).  Each town then sums the s smallest of its k distances.
 *
 * solver() takes the raw town types and road list, so the graph and every BFS
 * happen inside it; main() only reads and prints.
 */

#include <stdio.h>
#include <stdlib.h>

#define MAXN 100005
#define MAXM 100005
#define MAXK 105

/* file-scope work arrays, rebuilt on every call */
static int head_[MAXN], nxt_[2 * MAXM], to_[2 * MAXM];
static int queue_[MAXN];
static int dist_[MAXK][MAXN];             /* dist_[c][v], types are 1..k */
static int tmp_[MAXK];

static int cmp_int(const void *a, const void *b)
{
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

/* bfs_type: multi-source BFS from all towns producing type c, into dist. */
static void bfs_type(int n, const int *a, int c, int *dist)
{
    for (int v = 1; v <= n; v++)
        dist[v] = -1;
    int qh = 0, qt = 0;
    for (int v = 1; v <= n; v++)
        if (a[v] == c) {
            dist[v] = 0;
            queue_[qt] = v;
            qt = qt + 1;
        }
    while (qh < qt) {
        int u = queue_[qh];
        qh = qh + 1;
        for (int e = head_[u]; e != -1; e = nxt_[e]) {
            int v = to_[e];
            if (dist[v] < 0) {
                dist[v] = dist[u] + 1;
                queue_[qt] = v;
                qt = qt + 1;
            }
        }
    }
}

/* solver: reads no input.  cost[v] = cheapest way for town v to collect s of
 * the k goods types, given the town types a[1..n] and the m roads eu[]-ev[].
 * Writes the file-scope work arrays above. */
static void solver(int n, int m, int k, int s, const int *a,
                   const int *eu, const int *ev, long long *cost)
{
    for (int v = 1; v <= n; v++)
        head_[v] = -1;
    for (int i = 0; i < m; i++) {         /* undirected, two arcs per road */
        int e = 2 * i;
        to_[e] = ev[i]; nxt_[e] = head_[eu[i]]; head_[eu[i]] = e;
        to_[e + 1] = eu[i]; nxt_[e + 1] = head_[ev[i]]; head_[ev[i]] = e + 1;
    }
    for (int c = 1; c <= k; c++)
        bfs_type(n, a, c, dist_[c]);
    for (int v = 1; v <= n; v++) {
        for (int c = 1; c <= k; c++)
            tmp_[c - 1] = dist_[c][v];
        qsort(tmp_, k, sizeof *tmp_, cmp_int);
        long long sum = 0;
        for (int i = 0; i < s; i++)
            sum += tmp_[i];
        cost[v] = sum;
    }
}

int main(void)
{
    int n, m, k, s;
    if (scanf("%d %d %d %d", &n, &m, &k, &s) != 4)
        return 0;
    static int a[MAXN], eu[MAXM], ev[MAXM];
    static long long cost[MAXN];
    for (int v = 1; v <= n; v++)
        scanf("%d", &a[v]);
    for (int i = 0; i < m; i++)
        scanf("%d %d", &eu[i], &ev[i]);
    solver(n, m, k, s, a, eu, ev, cost);
    for (int v = 1; v <= n; v++)
        printf("%lld%c", cost[v], v == n ? '\n' : ' ');
    return 0;
}
