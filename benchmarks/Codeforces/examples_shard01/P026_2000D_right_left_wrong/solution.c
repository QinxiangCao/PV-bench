/*
 * Codeforces 2000/D - Right Left Wrong  (rating 1200, GREEDY)
 *
 * All a_i are positive, so a segment is worth taking whenever it exists.
 * Pairing the outermost 'L' with the outermost 'R', then the next pair inside,
 * and so on, covers the largest possible total: nested pairs never conflict
 * and any crossing pairing covers no more cells.
 */

#include <stdio.h>

/* solver: pure.  Maximum score for strip a[0..n-1] with letters s[0..n-1]. */
static long long solver(const int *a, const char *s, int n, long long *pre)
{
    pre[0] = 0;
    for (int i = 0; i < n; i++)
        pre[i + 1] = pre[i] + a[i];

    long long score = 0;
    int l = 0, r = n - 1;
    while (l < r) {
        while (l < r && s[l] != 'L')
            l++;
        while (l < r && s[r] != 'R')
            r--;
        if (l < r) {
            score += pre[r + 1] - pre[l];
            l++;
            r--;
        }
    }
    return score;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static int a[200005];
    static char s[200005];
    static long long pre[200006];
    while (t--) {
        int n;
        scanf("%d", &n);
        for (int i = 0; i < n; i++)
            scanf("%d", &a[i]);
        scanf("%200004s", s);
        printf("%lld\n", solver(a, s, n, pre));
    }
    return 0;
}
