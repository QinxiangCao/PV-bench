/*
 * Codeforces 1382/A - Common Subsequence  (rating 800, BRUTE FORCE)
 *
 * A common subsequence of minimum length has length 1 whenever the two arrays
 * share any value at all, so it is enough to look for one common element; if
 * none exists no common non-empty subsequence exists either.
 */

#include <stdio.h>
#include <string.h>

#define MAXV 1001

/* solver: pure.  Returns a value present in both arrays, or 0 if there is
 * none (values are >= 1, so 0 is safe as "not found"). */
static int solver(const int *a, int n, const int *b, int m)
{
    char seen[MAXV];
    memset(seen, 0, sizeof seen);
    for (int i = 0; i < n; i++)
        seen[a[i]] = 1;
    for (int j = 0; j < m; j++)
        if (seen[b[j]])
            return b[j];
    return 0;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    while (t--) {
        int n, m;
        static int a[1005], b[1005];
        scanf("%d %d", &n, &m);
        for (int i = 0; i < n; i++)
            scanf("%d", &a[i]);
        for (int j = 0; j < m; j++)
            scanf("%d", &b[j]);
        int v = solver(a, n, b, m);
        if (v)
            printf("YES\n1 %d\n", v);
        else
            printf("NO\n");
    }
    return 0;
}
