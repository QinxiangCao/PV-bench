/*
 * Codeforces 1725/B - Basketball Together  (rating 1000, GREEDY)
 *
 * Every member of a team is boosted to the leader's power P, so a team led by
 * P wins iff it fields floor(D/P)+1 players.  Sort by decreasing power and let
 * the strongest players lead in turn, padding each team with the weakest
 * players left: strong leaders need the fewest bodies, and only the head count
 * matters for the padding.
 */

// #include <stdio.h>
// #include <stdlib.h>

/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (mono_noninc : list Z -> Prop)
*/
/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P013_1725B_basketball_together.rocq.spec_lib */

void quicksort_desc(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 100000 &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_noninc(l1) &&
        IntArray::full(arr, n, l1)
*/
;


// static int cmp_desc(const void *x, const void *y)
// {
//     int a = *(const int *)x, b = *(const int *)y;
//     return (a < b) - (a > b);
// }

/* solver: maximum number of winning teams.  Sorts p[] in place (descending). */
static int solver(int *p, int n, int d)
/*@ With (powers : list Z)
    Require
      1 <= d && d <= 1000000000 &&
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (1 <= powers[i] && powers[i] <= 1000000000)) &&
      n == Zlength(powers) && IntArray::full(p, n, powers)
    Ensure
      Spec(d, powers, __return) &&
      exists (p_after : list Z), Permutation(powers, p_after) && IntArray::full(p, n, p_after)
*/
{
    // qsort(p, n, sizeof *p, cmp_desc);
    quicksort_desc(p, n);
    int wins = 0;
    long long used = 0;                 /* players committed to teams so far */
    for (int i = 0; i < n; i++) {
        long long need = (long long)d / p[i] + 1;   /* members incl. leader */
        if (used + need > n)
            break;                      /* weaker leaders only need more */
        wins++;
        used += need;
    }
    return wins;
}

// int main(void)
// {
//     int n, d;
//     if (scanf("%d %d", &n, &d) != 2)
//         return 0;
//     static int p[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &p[i]);
//     printf("%d\n", solver(p, n, d));
//     return 0;
// }
