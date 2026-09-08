/* Codeforces 1946/C - Tree Cutting */
#include <stdio.h>
#include <stdlib.h>

static int n, k, *head, *to, *next_edge, *parent, *order, *size_sub;

static int feasible(int minimum)
{
    for (int i = 0; i < n; ++i) size_sub[i] = 1;
    int components = 0;
    for (int oi = n - 1; oi >= 0; --oi) {
        int v = order[oi];
        if (size_sub[v] >= minimum) { ++components; size_sub[v] = 0; }
        if (parent[v] >= 0) size_sub[parent[v]] += size_sub[v];
    }
    return components >= k + 1;
}

static int solver(int nn, int kk, const int *eu, const int *ev)
{
    n = nn; k = kk;
    head = malloc((size_t)n * sizeof(*head)); to = malloc((size_t)(2*n-2) * sizeof(*to)); next_edge = malloc((size_t)(2*n-2) * sizeof(*next_edge));
    for (int i = 0; i < n; ++i) head[i] = -1;
    int ec = 0; for (int i = 0; i + 1 < n; ++i) { int u=eu[i],v=ev[i]; to[ec]=v;next_edge[ec]=head[u];head[u]=ec++;to[ec]=u;next_edge[ec]=head[v];head[v]=ec++; }
    parent = malloc((size_t)n * sizeof(*parent)); order = malloc((size_t)n * sizeof(*order)); size_sub = malloc((size_t)n * sizeof(*size_sub));
    int top = 1; order[0] = 0; parent[0] = -1;
    for (int i = 0; i < top; ++i) { int v=order[i]; for(int e=head[v];e!=-1;e=next_edge[e]) if(to[e]!=parent[v]) {parent[to[e]]=v;order[top++]=to[e];} }
    int lo=1, hi=n/(k+1), ans=1; while(lo<=hi){int mid=(lo+hi)/2;if(feasible(mid)){ans=mid;lo=mid+1;}else hi=mid-1;}
    free(head);free(to);free(next_edge);free(parent);free(order);free(size_sub); return ans;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        scanf("%d %d", &n, &k); int *eu=malloc((size_t)(n-1)*sizeof(*eu)),*ev=malloc((size_t)(n-1)*sizeof(*ev));
        for (int i = 0; i + 1 < n; ++i) { scanf("%d %d", &eu[i],&ev[i]); --eu[i];--ev[i]; }
        printf("%d\n",solver(n,k,eu,ev)); free(eu);free(ev);
    }
    return 0;
}
