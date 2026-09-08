/*
 * Codeforces 753/A - Santa Claus and Candies  (rating 1000, GREEDY)
 *
 * Handing out 1, 2, 3, ... keeps the totals as small as possible, so the
 * largest k is the one with k(k+1)/2 <= n.  Give 1..k and add the leftover
 * n - k(k+1)/2 (which is < k+1) to the last child, keeping all values distinct.
 */

#include <stdio.h>

/* solver: pure.  Fills out[] with the gift sizes and returns their count. */
static int solver(int n, int *out)
{
    int k = 0;
    long long used = 0;
    while (used + (k + 1) <= n) {
        k++;
        used += k;
    }
    for (int i = 0; i < k; i++)
        out[i] = i + 1;
    out[k - 1] += (int)(n - used);
    return k;
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static int out[100];
    int k = solver(n, out);
    printf("%d\n", k);
    for (int i = 0; i < k; i++)
        printf("%d%c", out[i], i + 1 == k ? '\n' : ' ');
    return 0;
}
