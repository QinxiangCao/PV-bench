/* Codeforces 1705/C - Mark and His Unfinished Essay */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void solver(const char *s, int c, const long long *l, const long long *r,
                   int q, const long long *queries, char *answers)
{
    long long before[40], length = (long long)strlen(s);
    for (int i = 0; i < c; ++i) { before[i] = length; length += r[i] - l[i] + 1; }
    for (int z = 0; z < q; ++z) {
        long long k = queries[z];
        for (int i = c - 1; i >= 0; --i) if (k > before[i]) k = l[i] + k - before[i] - 1;
        answers[z] = s[k - 1];
    }
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n, c, q; scanf("%d %d %d", &n, &c, &q);
        char *s = malloc((size_t)n + 1); scanf("%s", s);
        long long l[40], r[40];
        for (int i = 0; i < c; ++i) {
            scanf("%lld %lld", &l[i], &r[i]);
        }
        long long *queries = malloc((size_t)q * sizeof(*queries)); char *answers = malloc((size_t)q);
        for (int i = 0; i < q; ++i) scanf("%lld", &queries[i]);
        solver(s, c, l, r, q, queries, answers);
        for (int i = 0; i < q; ++i) printf("%c\n", answers[i]);
        free(answers); free(queries);
        free(s);
    }
    return 0;
}
