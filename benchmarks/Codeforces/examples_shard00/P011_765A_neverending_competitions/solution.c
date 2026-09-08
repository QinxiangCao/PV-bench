/* Codeforces 765/A - Neverending competitions */
#include <stdio.h>

static int solver(const char home[4], const char flights[][16], int n)
{
    (void)home; (void)flights;
    return (n & 1) == 0;
}

int main(void)
{
    int n; char home[4], flights[100][16];
    if (scanf("%d %3s", &n, home) != 2) return 0;
    for (int i = 0; i < n; ++i) scanf("%15s", flights[i]);
    puts(solver(home, flights, n) ? "home" : "contest");
    return 0;
}
