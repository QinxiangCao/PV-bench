/*
 * Codeforces 433/A - Kitahara Haruki's Gift  (rating 1100, BRUTE FORCE)
 *
 * Work in units of 100 grams, so weights are 1 and 2 and the total is at most
 * 200.  A subset-sum bitmask over the reachable half-weights decides whether
 * one friend can receive exactly half of the total.
 */

#include <stdio.h>
#include <string.h>

/* solver: pure.  1 if the apples w[0..n-1] (100 or 200 g) split evenly. */
static int solver(const int *w, int n)
{
    int total = 0;
    for (int i = 0; i < n; i++)
        total += w[i] / 100;
    if (total % 2)
        return 0;
    char reach[205];
    memset(reach, 0, sizeof reach);
    reach[0] = 1;
    for (int i = 0; i < n; i++) {
        int u = w[i] / 100;
        for (int s = total; s >= u; s--)
            if (reach[s - u])
                reach[s] = 1;
    }
    return reach[total / 2];
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static int w[105];
    for (int i = 0; i < n; i++)
        scanf("%d", &w[i]);
    puts(solver(w, n) ? "YES" : "NO");
    return 0;
}
