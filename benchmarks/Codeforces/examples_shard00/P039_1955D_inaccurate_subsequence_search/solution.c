/* Codeforces 1955/D - Inaccurate Subsequence Search */
#include <stdio.h>
#include <stdlib.h>

#define MAXA 1000000
static int need[MAXA + 1], have[MAXA + 1];

static int minimum(int a, int b) { return a < b ? a : b; }

static int solver(const int *a, int n, const int *b, int m, int k)
{
    for (int i = 0; i < m; ++i) ++need[b[i]];
    int matched = 0, answer = 0;
    for (int i = 0; i < m; ++i) { int v = a[i]; matched -= minimum(have[v], need[v]); ++have[v]; matched += minimum(have[v], need[v]); }
    if (matched >= k) ++answer;
    for (int i = m; i < n; ++i) {
        int v = a[i - m]; matched -= minimum(have[v], need[v]); --have[v]; matched += minimum(have[v], need[v]);
        v = a[i]; matched -= minimum(have[v], need[v]); ++have[v]; matched += minimum(have[v], need[v]);
        if (matched >= k) ++answer;
    }
    for (int i = 0; i < n; ++i) have[a[i]] = 0;
    for (int i = 0; i < m; ++i) need[b[i]] = 0;
    return answer;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, m, k; scanf("%d %d %d", &n, &m, &k);
        int *a = malloc((size_t)n * sizeof(*a));
        int *b = malloc((size_t)m * sizeof(*b));
        for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
        for (int i = 0; i < m; ++i) scanf("%d", &b[i]);
        printf("%d\n", solver(a, n, b, m, k));
        free(a); free(b);
    }
    return 0;
}
