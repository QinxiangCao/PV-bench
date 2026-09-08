/*
 * Codeforces 837/C - Two Seals  (rating 1500, BRUTE FORCE)
 *
 * n <= 100, so try every pair of seals and every combination of rotations.
 * Two axis-parallel rectangles fit on the sheet without overlapping iff they
 * can be stacked side by side or one above the other.
 */

#include <stdio.h>

/* fits: can w1 x h1 and w2 x h2 sit inside a x b without overlapping? */
static int fits(int w1, int h1, int w2, int h2, int a, int b)
{
    if (w1 + w2 <= a && (h1 > h2 ? h1 : h2) <= b)
        return 1;                          /* side by side */
    if (h1 + h2 <= b && (w1 > w2 ? w1 : w2) <= a)
        return 1;                          /* stacked */
    return 0;
}

/* solver: pure.  Largest total area of two non-overlapping seals on a x b. */
static int solver(const int *x, const int *y, int n, int a, int b)
{
    int best = 0;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            for (int ri = 0; ri < 2; ri++)
                for (int rj = 0; rj < 2; rj++) {
                    int w1 = ri ? y[i] : x[i], h1 = ri ? x[i] : y[i];
                    int w2 = rj ? y[j] : x[j], h2 = rj ? x[j] : y[j];
                    if (fits(w1, h1, w2, h2, a, b)) {
                        int area = w1 * h1 + w2 * h2;
                        if (area > best)
                            best = area;
                    }
                }
    return best;
}

int main(void)
{
    int n, a, b;
    if (scanf("%d %d %d", &n, &a, &b) != 3)
        return 0;
    static int x[105], y[105];
    for (int i = 0; i < n; i++)
        scanf("%d %d", &x[i], &y[i]);
    printf("%d\n", solver(x, y, n, a, b));
    return 0;
}
