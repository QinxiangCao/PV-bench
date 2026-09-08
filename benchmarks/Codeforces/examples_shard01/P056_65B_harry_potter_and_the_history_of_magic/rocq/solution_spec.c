/*
 * Codeforces 65/B - Harry Potter and the History of Magic  (rating 1700, GREEDY)
 *
 * Process the dates left to right keeping the smallest legal value: a smaller
 * current date never constrains later ones more.  For each date try every
 * one-digit edit (and no edit at all), keep those inside [1000, 2011] that are
 * at least the previous value, and take the minimum.
 */

// #include <stdio.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P056_65B_harry_potter_and_the_history_of_magic.rocq.spec_lib */
/*@ Extern Coq
      (Spec : list Z -> option(list Z) -> Prop)
*/

/* solver: pure.  Smallest value in [1000, 2011] that is >= prev and differs
 * from y in at most one digit, or -1 if there is none. */
static int next_year(int y, int prev)
{
    int d[4] = {y / 1000, y / 100 % 10, y / 10 % 10, y % 10};
    int best = -1;
    for (int pos = 0; pos < 4; pos++) {
        int old = d[pos];
        for (int v = (pos == 0 ? 1 : 0); v <= 9; v++) {
            d[pos] = v;
            int cand = d[0] * 1000 + d[1] * 100 + d[2] * 10 + d[3];
            if (cand >= 1000 && cand <= 2011 && cand >= prev &&
                (best < 0 || cand < best))
                best = cand;
        }
        d[pos] = old;
    }
    return best;
}

/* solver: complete case.  Return 1 with the complete sequence, or 0 when the
 * frozen option-valued Spec requires None. */
static int solver(const int *years, int n, int *out)
/*@ With (input_years : list Z)
    Require
      1 <= n && n <= 1000 && (forall i, (0 <= i && i < n) => (1000 <= input_years[i] && input_years[i] <= 9999)) && n == Zlength(input_years) && IntArray::full(years, n, input_years) * IntArray::full_shape(out, n)
    Ensure
      ((__return == 0 && Spec(input_years, None) && IntArray::full_shape(out, n)) || (exists (result : list Z), __return == 1 && Spec(input_years, Some(result)) && IntArray::full(out, n, result))) && IntArray::full(years, n, input_years)
*/
{
    int prev = 1000;
    for (int i = 0; i < n; i++) {
        out[i] = next_year(years[i], prev);
        if (out[i] < 0)
            return 0;
        prev = out[i];
    }
    return 1;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int y[1005], z[1005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &y[i]);
//     int ok = solver(y, n, z);
//     if (!ok) {
//         puts("No solution");
//         return 0;
//     }
//     for (int i = 0; i < n; i++)
//         printf("%d\n", z[i]);
//     return 0;
// }
