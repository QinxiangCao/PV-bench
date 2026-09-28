#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

typedef long long i64;
static i64 gcdll(i64 a, i64 b)

{

    while (b)
    {
        i64 t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static int cmpi(const void *A, const void *B)

{
    return *(const int *)A - *(const int *)B;
}
static int solver(int n, int k,
                  const i64 *a)

{
    int allone = 1;

    for (int i = 0; i < n; i++)
        if (a[i] != 1)
            allone = 0;
    if (allone)
        return k == n ? 0 : n - k;
    int sad = 0, two = 0;

    for (int i = 0; i + 1 < n; i++)
        if (gcdll(a[i], a[i + 1]) == 1)
            sad++;

    for (int i = 0; i < n;)
    {
        if (a[i] == 1)
        {
            i++;
            continue;
        }
        int run = 0;

        while (i + 1 < n && a[i + 1] != 1)
        {
            if (gcdll(a[i], a[i + 1]) == 1)
                run++;
            else
            {
                two += run / 2;
                run = 0;
            }
            i++;
        }
        two += run / 2;
        i++;
    }

    int *ones = malloc((size_t)n * sizeof *ones)
        , oc = 0;

    for (int i = 0; i < n;)
    {
        if (a[i] != 1)
        {
            i++;
            continue;
        }
        int l = i;

        while (i < n && a[i] == 1)
            i++;
        if (l > 0 && i < n)
        {
            ones[oc] = i - l;
            oc++;
        }
    }

    int use = k < two ? k : two;
    sad -= 2 * use;
    k -= use;
    qsort(ones, oc, sizeof *ones, cmpi);

    for (int i = 0; i < oc && ones[i] <= k; i++)
    {
        k -= ones[i];
        sad -= ones[i] + 1;
    }
    if (k > sad)
        k = sad;
    sad -= k;
    if (sad < 0)
        sad = 0;

    free(ones);
    return sad;
}
int main(void)
{
    int T;
    if (scanf("%d", &T) != 1)
        return 0;
    while (T--)
    {
        int n, k;
        scanf("%d%d", &n, &k);
        i64 *a = malloc((size_t)n * sizeof *a);
        for (int i = 0; i < n; i++)
            scanf("%lld", &a[i]);
        printf("%d\n", solver(n, k, a));
        free(a);
    }
    return 0;
}
