/* Codeforces 1992/F - Valuable Cards */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

static int solver(const int *a, int n,
                  int x)

{
    unsigned char *used = calloc((size_t)x + 1, 1)
        ;
    int *products_buf = malloc((size_t)(x + 1) * sizeof(*products_buf))
        ;
    int count = 1, segments = 1;
    products_buf[0] = 1;
    used[1] = 1;

    for (int i = 0; i < n; ++i)
    {
        int v = a[i];
        if (x % v)
            continue;
        int old = count, reaches = 0;

        for (int j = 0; j < old; ++j)

            if (products_buf[j] <= x / v && x % (products_buf[j] * v) == 0)
            {
                int p = products_buf[j] * v;

                if (!used[p])
                {
                    used[p] = 1;
                    products_buf[count] = p;

                    ++count;
                }
                if (p == x)
                    reaches = 1;
            }

        if (reaches)
        {
            ++segments;

            for (int j = 0; j < count; ++j)
                used[products_buf[j]] = 0;
            count = 1;
            products_buf[0] = 1;
            used[1] = 1;

            if (!used[v])
            {
                used[v] = 1;
                products_buf[count] = v;

                ++count;
            }
        }
    }

    free(used)
        ;
    free(products_buf)
        ;
    return segments;
}
int main(void)
{
    int t;
    scanf("%d", &t);
    while (t--)
    {
        int n, x;
        scanf("%d %d", &n, &x);
        int *a = malloc((size_t)n * sizeof(*a));
        for (int i = 0; i < n; ++i)
            scanf("%d", &a[i]);
        printf("%d\n", solver(a, n, x));
        free(a);
    }
    return 0;
}
