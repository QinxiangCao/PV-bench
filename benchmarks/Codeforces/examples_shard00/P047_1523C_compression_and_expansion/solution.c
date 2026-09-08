/* Codeforces 1523/C - Compression and Expansion */
#include <stdio.h>
#include <stdlib.h>

static int solver(const int *values, int n, int *flat, int *lengths)
{
    int stack[1005], depth = 0, total = 0;
    for (int line = 0; line < n; ++line) {
        int x = values[line];
        if (x == 1) stack[depth++] = 1;
        else { while (depth && stack[depth - 1] + 1 != x) --depth; stack[depth - 1] = x; }
        lengths[line] = depth;
        for (int i = 0; i < depth; ++i) flat[total++] = stack[i];
    }
    return total;
}

int main(void)
{
    int t; scanf("%d", &t);
    while (t--) {
        int n; scanf("%d", &n); int *values = malloc((size_t)n * sizeof(*values));
        int *lengths = malloc((size_t)n * sizeof(*lengths)); int *flat = malloc((size_t)n * n * sizeof(*flat));
        for (int i = 0; i < n; ++i) scanf("%d", &values[i]); solver(values, n, flat, lengths);
        int at = 0; for (int line = 0; line < n; ++line)
            for (int i = 0; i < lengths[line]; ++i) printf("%d%c", flat[at++], i + 1 == lengths[line] ? '\n' : '.');
        free(flat); free(lengths); free(values);
    }
    return 0;
}
