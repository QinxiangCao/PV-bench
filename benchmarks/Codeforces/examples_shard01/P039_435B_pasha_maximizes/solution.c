/*
 * Codeforces 435/B - Pasha Maximizes  (rating 1400, GREEDY)
 *
 * Fill the number left to right: for each position take the largest digit
 * still reachable within the remaining swap budget (it sits at most k places
 * to the right) and bubble it into place, paying its distance.
 */

#include <stdio.h>
#include <string.h>

/* solver: rearranges the digit string d in place using at most k adjacent
 * swaps to make it as large as possible. */
static void solver(char *d, int n, int k)
{
    for (int i = 0; i < n && k > 0; i++) {
        int best = i;
        for (int j = i + 1; j < n && j - i <= k; j++)
            if (d[j] > d[best])
                best = j;
        for (int j = best; j > i; j--) {
            char tmp = d[j];
            d[j] = d[j - 1];
            d[j - 1] = tmp;
            k--;
        }
    }
}

int main(void)
{
    static char d[32];
    int k;
    if (scanf("%31s %d", d, &k) != 2)
        return 0;
    solver(d, (int)strlen(d), k);
    puts(d);
    return 0;
}
