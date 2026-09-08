/*
 * Codeforces 707/A - Brain's Photos  (rating 800, IMPLEMENTATION)
 *
 * The photo is coloured iff at least one pixel is cyan, magenta or yellow;
 * white / grey / black alone make it black-and-white.
 */

#include <stdio.h>

/* solver: pure.  px holds n*m pixel letters; 1 if the photo is coloured. */

static int solver(const char *px, int n, int m)
{
    for (int i = 0; i < n * m; i++)
        if (px[i] == 'C' || px[i] == 'M' || px[i] == 'Y')
            return 1;
    return 0;
}

int main(void)
{
    int n, m;
    if (scanf("%d %d", &n, &m) != 2)
        return 0;
    static char px[10005];
    for (int i = 0; i < n * m; i++)
        scanf(" %c", &px[i]);
    puts(solver(px, n, m) ? "#Color" : "#Black&White");
    return 0;
}
