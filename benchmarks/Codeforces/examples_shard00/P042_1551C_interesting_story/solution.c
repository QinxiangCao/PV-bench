/* Codeforces 1551/C - Interesting Story */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int cmp_desc(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (b > a) - (b < a);
}

static int solver(char *const *words, int n)
{
    int *score = malloc((size_t)5 * n * sizeof(*score));
    for (int i = 0; i < n; ++i) {
        int len = (int)strlen(words[i]), cnt[5] = {0};
        for (int j = 0; j < len; ++j) ++cnt[words[i][j] - 'a'];
        for (int c = 0; c < 5; ++c) score[c * n + i] = 2 * cnt[c] - len;
    }
    int answer = 0;
    for (int c = 0; c < 5; ++c) {
        qsort(score + c * n, (size_t)n, sizeof(*score), cmp_desc);
        int sum = 0, take = 0;
        while (take < n && sum + score[c * n + take] > 0) sum += score[c * n + take++];
        if (take > answer) answer = take;
    }
    free(score); return answer;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; scanf("%d", &n); char **words = malloc((size_t)n * sizeof(*words));
        for (int i = 0; i < n; ++i) { words[i] = malloc(200005); scanf("%200004s", words[i]); }
        printf("%d\n", solver(words, n));
        for (int i = 0; i < n; ++i) free(words[i]); free(words);
    }
    return 0;
}
