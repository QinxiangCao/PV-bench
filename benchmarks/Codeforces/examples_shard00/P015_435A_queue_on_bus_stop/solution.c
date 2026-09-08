/* Codeforces 435/A - Queue on Bus Stop */
#include <stdio.h>

static int solver(const int *groups, int n, int capacity)
{
    int buses = 1, used = 0;
    for (int i = 0; i < n; ++i) {
        if (used + groups[i] > capacity) { ++buses; used = 0; }
        used += groups[i];
    }
    return buses;
}

int main(void)
{
    int n, m, groups[100];
    if (scanf("%d %d", &n, &m) != 2) return 0;
    for (int i = 0; i < n; ++i) scanf("%d", &groups[i]);
    printf("%d\n", solver(groups, n, m));
    return 0;
}
