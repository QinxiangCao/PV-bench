/* Codeforces 450/A - Jzzhu and Children */
#include <stdio.h>

static int solver(const int *wants, int n, int m)
{
    int answer = 1, best = 0;
    for (int i = 0; i < n; ++i) {
        int turns = (wants[i] + m - 1) / m;
        if (turns >= best) { best = turns; answer = i + 1; }
    }
    return answer;
}

int main(void)
{
    int n, m, wants[100];
    if (scanf("%d %d", &n, &m) != 2) return 0;
    for (int i = 0; i < n; ++i) scanf("%d", &wants[i]);
    printf("%d\n", solver(wants, n, m));
    return 0;
}
