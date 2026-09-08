/*
 * Codeforces 985/A - Chess Placing  (rating 1100, IMPLEMENTATION)
 *
 * The pieces must land on the n/2 black cells (1,3,5,...) or the n/2 white
 * cells (2,4,6,...).  Pieces never need to cross, so matching the sorted
 * pieces to the sorted targets in order is optimal; take the cheaper colour.
 */

// #include <stdio.h>
// #include <stdlib.h>

/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P023_985A_chess_placing.rocq.spec_lib */
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 50000 &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        IntArray::full(arr, n, l1)
*/
;

// static int cmp_int(const void *a, const void *b)
// {
//     int x = *(const int *)a, y = *(const int *)b;
//     return (x > y) - (x < y);
// }

static int iabs(int x)
{
    return x < 0 ? -x : x;
}

/* solver: minimum moves to gather the pieces on one colour.  Sorts p[]. */
static long long solver(int *p, int half)
/*@ With (positions : list Z)
    Require
      2 <= 2 * half && 2 * half <= 100 &&
      Pre(2 * half, positions) && (forall i, (0 <= i && i < half) => (1 <= positions[i] && positions[i] <= 2 * half)) &&
      half == Zlength(positions) && IntArray::full(p, half, positions)
    Ensure
      Spec(2 * half, positions, __return) &&
      exists (p_after : list Z), Permutation(positions, p_after) && IntArray::full(p, half, p_after)
*/
{
    // qsort(p, half, sizeof *p, cmp_int);
    quicksort(p, half);
    long long odd = 0, even = 0;
    for (int i = 0; i < half; i++) {
        odd += iabs(p[i] - (2 * i + 1));       /* black cells 1,3,5,... */
        even += iabs(p[i] - (2 * i + 2));      /* white cells 2,4,6,... */
    }
    return odd < even ? odd : even;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int p[55];
//     int half = n / 2;
//     for (int i = 0; i < half; i++)
//         scanf("%d", &p[i]);
//     printf("%lld\n", solver(p, half));
//     return 0;
// }
