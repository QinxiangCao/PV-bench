/* Codeforces 1082/C - Multi-Subject Competition */
#include <stdio.h>
#include <stdlib.h>

typedef struct { int subject, skill; } Candidate;

static int cmp_candidate(const void *x, const void *y)
{
    const Candidate *a = x, *b = y;
    if (a->subject != b->subject) return (a->subject > b->subject) - (a->subject < b->subject);
    return (b->skill > a->skill) - (b->skill < a->skill);
}

static long long solver(Candidate *a, int n, int m)
{
    (void)m; long long *total = calloc((size_t)n + 1, sizeof(*total));
    qsort(a, (size_t)n, sizeof(*a), cmp_candidate);
    for (int i = 0; i < n;) {
        int j = i; long long prefix = 0;
        while (j < n && a[j].subject == a[i].subject) {
            prefix += a[j].skill; ++j; if (prefix > 0) total[j - i] += prefix;
        }
        i = j;
    }
    long long answer = 0; for (int k = 1; k <= n; ++k) if (total[k] > answer) answer = total[k];
    free(total); return answer;
}

int main(void)
{
    int n, m; if (scanf("%d %d", &n, &m) != 2) return 0;
    Candidate *a = malloc((size_t)n * sizeof(*a));
    for (int i = 0; i < n; ++i) scanf("%d %d", &a[i].subject, &a[i].skill);
    printf("%lld\n", solver(a, n, m)); free(a);
    return 0;
}
