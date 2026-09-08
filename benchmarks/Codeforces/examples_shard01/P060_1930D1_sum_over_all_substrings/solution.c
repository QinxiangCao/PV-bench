/*
 * Codeforces 1930/D1 - Sum over all Substrings (Easy)  (rating 1800, OTHER)
 *
 * f(p) (minimum 1s in a p-good string) is computed greedily: scan left to
 * right; whenever an uncovered '1' is seen at position k, place a single 1 that
 * covers positions k, k+1, k+2 (advance the cover to k+2), counting one. This
 * greedy is prefix-consistent, so for a fixed left end i the running count
 * equals f(s[i..k]); summing over all k and all i gives the answer.
 */

#include <stdio.h>

/* solver: pure. Returns the sum of f over all substrings of s[0..n-1]. */
static long long solver(const char *s, int n)
{
    long long total = 0;
    for (int i = 0; i < n; i++) {
        int cover = i - 1;        /* positions <= cover already accounted for */
        long long cnt = 0;
        for (int k = i; k < n; k++) {
            if (s[k] == '1' && k > cover) { cnt++; cover = k + 2; }
            total += cnt;         /* cnt == f(s[i..k]) */
        }
    }
    return total;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    while (t--) {
        int n;
        char s[105];
        scanf("%d %104s", &n, s);
        printf("%lld\n", solver(s, n));
    }
    return 0;
}
