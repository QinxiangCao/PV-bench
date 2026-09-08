/* Codeforces 1696/B - NIT Destroys the Universe */
#include <stdio.h>

static int solver(const int *a, int n)
{
    int runs = 0, inside = 0;
    for (int i = 0; i < n; ++i) {
        if (a[i] != 0 && !inside) { ++runs; inside = 1; }
        if (a[i] == 0) inside = 0;
    }
    return runs > 2 ? 2 : runs;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, a[200005]; scanf("%d", &n);
        for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
        printf("%d\n", solver(a, n));
    }
    return 0;
}
