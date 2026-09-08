/*
 * Codeforces 985/A - Chess Placing  (rating 1100, IMPLEMENTATION)
 *
 * The pieces must land on the n/2 black cells (1,3,5,...) or the n/2 white
 * cells (2,4,6,...).  Pieces never need to cross, so matching the sorted
 * pieces to the sorted targets in order is optimal; take the cheaper colour.
 */

#include <stdio.h>
#include <stdlib.h>

static int cmp_int(const void *a, const void *b)
{
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

static int iabs(int x)
{
    return x < 0 ? -x : x;
}

/* solver: minimum moves to gather the pieces on one colour.  Sorts p[]. */
static long long solver(int *p, int half)
{
    qsort(p, half, sizeof *p, cmp_int);
    long long odd = 0, even = 0;
    for (int i = 0; i < half; i++) {
        odd += iabs(p[i] - (2 * i + 1));       /* black cells 1,3,5,... */
        even += iabs(p[i] - (2 * i + 2));      /* white cells 2,4,6,... */
    }
    return odd < even ? odd : even;
}

int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    static int p[55];
    int half = n / 2;
    for (int i = 0; i < half; i++)
        scanf("%d", &p[i]);
    printf("%lld\n", solver(p, half));
    return 0;
}
