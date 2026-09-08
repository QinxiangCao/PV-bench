/*
 * Codeforces 1031/A - Golden Plate  (rating 800, MATH)
 *
 * Ring i lies on the border of the (w-4(i-1)) x (h-4(i-1)) rectangle, and the
 * border of a W x H rectangle holds 2*(W+H) - 4 cells.  Sum that over the k
 * rings; the constraint on k guarantees every inner rectangle stays valid.
 */

#include <stdio.h>

/* solver: pure.  Number of gilded cells for a w x h plate with k rings. */
static long long solver(int w, int h, int k)
{
    long long total = 0;
    for (int i = 0; i < k; i++) {
        long long W = w - 4LL * i, H = h - 4LL * i;
        total += 2 * (W + H) - 4;
    }
    return total;
}

int main(void)
{
    int w, h, k;
    if (scanf("%d %d %d", &w, &h, &k) != 3)
        return 0;
    printf("%lld\n", solver(w, h, k));
    return 0;
}
