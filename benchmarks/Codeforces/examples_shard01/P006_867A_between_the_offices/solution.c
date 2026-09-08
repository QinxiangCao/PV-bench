/*
 * Codeforces 867/A - Between the Offices  (rating 800, VERDICT)
 *
 * Given a chronological string of 'S' (Seattle) and 'F' (San Francisco),
 * decide whether there were more Seattle->SanFrancisco flights than the
 * reverse. That happens iff the first day is 'S' and the last day is 'F'.
 */

#include <stdio.h>
#include <string.h>

/* solver: pure. Returns 1 (YES) if first=='S' and last=='F', else 0. */
static int solver(const char *s, int n)
{
    return (s[0] == 'S' && s[n - 1] == 'F');
}

int main(void)
{
    int n;
    char s[128];
    if (scanf("%d %127s", &n, s) != 2)
        return 0;

    printf("%s\n", solver(s, n) ? "YES" : "NO");
    return 0;
}
