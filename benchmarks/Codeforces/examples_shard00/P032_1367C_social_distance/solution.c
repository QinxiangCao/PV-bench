/* Codeforces 1367/C - Social Distance */
#include <stdio.h>
#include <stdlib.h>

static int solver(char *s, int n, int k)
{
    int answer = 0, last = -k - 1;
    int *next = malloc((size_t)n * sizeof(*next));
    int nearest = n + k;
    for (int i = n - 1; i >= 0; --i) {
        if (s[i] == '1') nearest = i;
        next[i] = nearest;
    }
    for (int i = 0; i < n; ++i) {
        if (s[i] == '1') { last = i; continue; }
        if (i - last > k && next[i] - i > k) { ++answer; last = i; }
    }
    free(next);
    return answer;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, k; char *s; scanf("%d %d", &n, &k);
        s = malloc((size_t)n + 1); scanf("%s", s);
        printf("%d\n", solver(s, n, k)); free(s);
    }
    return 0;
}
