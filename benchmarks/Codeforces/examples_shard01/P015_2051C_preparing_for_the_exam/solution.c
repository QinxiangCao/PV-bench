/*
 * Codeforces 2051/C - Preparing for the Exam  (rating 1000, IMPLEMENTATION)
 *
 * List i asks every question except a_i.  So Monocarp passes iff the set of
 * questions he does not know is empty, or is exactly {a_i}.
 */

#include <stdio.h>
#include <string.h>

/* solver: pure.  known[1..n] flags, a[0..m-1] the missing question per list;
 * fills res[0..m-1] with '1'/'0' and terminates it. */
static void solver(int n, const char *known, const int *a, int m, char *res)
{
    int unknown = 0, only = 0;
    for (int q = 1; q <= n; q++)
        if (!known[q]) {
            unknown++;
            only = q;
        }
    for (int i = 0; i < m; i++)
        res[i] = (unknown == 0 || (unknown == 1 && a[i] == only)) ? '1' : '0';
    res[m] = '\0';
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static int a[300005];
    static char known[300005], res[300006];
    while (t--) {
        int n, m, k;
        scanf("%d %d %d", &n, &m, &k);
        memset(known, 0, (size_t)n + 1);
        for (int i = 0; i < m; i++)
            scanf("%d", &a[i]);
        for (int i = 0; i < k; i++) {
            int q;
            scanf("%d", &q);
            known[q] = 1;
        }
        solver(n, known, a, m, res);
        puts(res);
    }
    return 0;
}
