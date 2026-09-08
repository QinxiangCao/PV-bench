/*
 * Codeforces 1725/B - Basketball Together  (rating 1000, GREEDY)
 *
 * Every member of a team is boosted to the leader's power P, so a team led by
 * P wins iff it fields floor(D/P)+1 players.  Sort by decreasing power and let
 * the strongest players lead in turn, padding each team with the weakest
 * players left: strong leaders need the fewest bodies, and only the head count
 * matters for the padding.
 */

#include <stdio.h>
#include <stdlib.h>

static int cmp_desc(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a < b) - (a > b);
}

/* solver: maximum number of winning teams.  Sorts p[] in place (descending). */
static int solver(int *p, int n, int d)
{
    qsort(p, n, sizeof *p, cmp_desc);
    int wins = 0;
    long long used = 0;                 /* players committed to teams so far */
    for (int i = 0; i < n; i++) {
        long long need = (long long)d / p[i] + 1;   /* members incl. leader */
        if (used + need > n)
            break;                      /* weaker leaders only need more */
        wins++;
        used += need;
    }
    return wins;
}

int main(void)
{
    int n, d;
    if (scanf("%d %d", &n, &d) != 2)
        return 0;
    static int p[100005];
    for (int i = 0; i < n; i++)
        scanf("%d", &p[i]);
    printf("%d\n", solver(p, n, d));
    return 0;
}
