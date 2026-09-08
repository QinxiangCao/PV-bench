/* Codeforces 1891/A - Sorting with Twos */
#include <stdio.h>

static int is_power_of_two(int x) { return x > 0 && (x & (x - 1)) == 0; }

static int solver(const int *a, int n)
{
    for (int i = 1; i < n; ++i)
        if (a[i - 1] > a[i] && !is_power_of_two(i)) return 0;
    return 1;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, a[20]; scanf("%d", &n);
        for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
        puts(solver(a, n) ? "YES" : "NO");
    }
    return 0;
}
