/* Codeforces 1890/A - Doremy's Paint 3 */
#include <stdio.h>

static int solver(const int *a, int n)
{
    int x = a[0], y = -1, cx = 0, cy = 0;
    for (int i = 0; i < n; ++i) {
        if (a[i] == x) ++cx;
        else if (y == -1 || a[i] == y) { y = a[i]; ++cy; }
        else return 0;
    }
    return cy == 0 || (cx - cy <= 1 && cy - cx <= 1);
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, a[100]; scanf("%d", &n);
        for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
        puts(solver(a, n) ? "YES" : "NO");
    }
    return 0;
}
