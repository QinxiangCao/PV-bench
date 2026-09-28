/* Codeforces 1416/C - XOR Inverse */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

static int *a, *tmp;
static long long cost[30][2];

static void solve(int l, int r, int bit)

{
    if (bit < 0 || r - l <= 1)
        return;
    long long zeros = 0, ones = 0;

    for (int i = l; i < r; i = i + 1)
    {
        if ((a[i] >> bit) & 1)
        {
            cost[bit][1] += zeros;
            ones = ones + 1;
        }
        else
        {
            cost[bit][0] += ones;
            zeros = zeros + 1;
        }
    }
    int p = l;

    for (int i = l; i < r; i = i + 1)
    {
        if (((a[i] >> bit) & 1) == 0)
        {
            tmp[p] = a[i];
            p = p + 1;
        }
    }
    int mid = p;

    for (int i = l; i < r; i = i + 1)
    {
        if ((a[i] >> bit) & 1)
        {

            tmp[p] = a[i];
            p = p + 1;
        }
    }

    for (int i = l; i < r; i = i + 1)
    {

        int value = tmp[i];

        a[i] = value;
    }
    solve(l, mid, bit - 1)
        ;

    solve(mid, r, bit - 1)
        ;
}
static void solver(const int *input, int n, long long *out_inv,
                   int *out_x)

{
    a = malloc((size_t)n * sizeof(*a))
        ;
    tmp = malloc((size_t)n * sizeof(*tmp))
        ;

    for (int i = 0; i < n; i = i + 1)
        a[i] = input[i];

    for (int b = 0; b < 30; b = b + 1)
    {

        cost[b][1] = 0;
        cost[b][0] = 0;
    }

    solve(0, n, 29) ;
    long long inv = 0;
    int x = 0;

    for (int b = 0; b < 30; b = b + 1)
    {

        if (cost[b][1] < cost[b][0])
        {
            inv += cost[b][1];
            x |= 1 << b;
        }
        else
            inv += cost[b][0];
    }
    *out_inv = inv;
    *out_x = x;

    free(a) ;
    free(tmp) ;
    a = 0;
    tmp = 0;
}
int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    int *input = malloc((size_t)n * sizeof(*input));
    for (int i = 0; i < n; ++i)
        scanf("%d", &input[i]);
    long long inv;
    int x;
    solver(input, n, &inv, &x);
    printf("%lld %d\n", inv, x);
    free(input);
    return 0;
}
