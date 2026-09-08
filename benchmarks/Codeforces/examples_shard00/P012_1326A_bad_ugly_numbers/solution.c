/* Codeforces 1326/A - Bad Ugly Numbers */
#include <stdio.h>

static int solver(int n, char *out)
{
    if (n == 1) return -1;
    out[0] = '2';
    for (int i = 1; i < n; ++i) out[i] = '3';
    out[n] = '\0';
    return n;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; static char out[100001]; scanf("%d", &n);
        if (solver(n, out) < 0) puts("-1"); else puts(out);
    }
    return 0;
}
