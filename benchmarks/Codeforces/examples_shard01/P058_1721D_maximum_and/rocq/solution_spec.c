/*
 * Codeforces 1721/D - Maximum AND  (rating 1800, BITMASKS)
 *
 * Build the answer greedily from the top bit down: a mask is achievable iff b
 * can be matched to a so that every pair XORs to a superset of the mask, i.e.
 * the multiset {a_i & mask} equals the multiset {~b_i & mask}.  Sorting both
 * lists and comparing tests that in O(n log n) per candidate bit.
 */

// #include <stdio.h>
// #include <stdlib.h>

/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P058_1721D_maximum_and.rocq.spec_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/

void quicksort(const unsigned *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 200000 &&
      UIntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        UIntArray::full(arr, n, l1)
*/
;

// static int cmp_uint(const void *x, const void *y)
// {
//     unsigned a = *(const unsigned *)x, b = *(const unsigned *)y;
//     return (a > b) - (a < b);
// }

/* feasible: can b be permuted so that (a_i ^ b_i) & mask == mask for all i? */
static int feasible(const unsigned *a, const unsigned *b, int n, unsigned mask,
                    unsigned *ka, unsigned *kb)
{
    for (int i = 0; i < n; i++) {
        ka[i] = a[i] & mask;
        kb[i] = (~b[i]) & mask;
    }
    // qsort(ka, n, sizeof *ka, cmp_uint);
    // qsort(kb, n, sizeof *kb, cmp_uint);
    quicksort(ka, n);
    quicksort(kb, n);
    for (int i = 0; i < n; i++)
        if (ka[i] != kb[i])
            return 0;
    return 1;
}

/* solver: maximum AND of the pairwise XORs over all pairings. */
static unsigned solver(const unsigned *a, const unsigned *b, int n,
                       unsigned *ka, unsigned *kb)
/*@ With (left : list Z) (right : list Z)
    Require
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (0 <= left[i] && left[i] < 1073741824)) && (forall i, (0 <= i && i < n) => (0 <= right[i] && right[i] < 1073741824)) &&
      n == Zlength(left) && Zlength(right) == n && UIntArray::full(a, n, left) * UIntArray::full(b, n, right) * UIntArray::undef_full(ka, n) * UIntArray::undef_full(kb, n)
    Ensure
      Spec(left, right, __return) &&
      UIntArray::full(a, n, left) * UIntArray::full(b, n, right) * UIntArray::full_shape(ka, n) * UIntArray::full_shape(kb, n)
*/
{
    unsigned ans = 0;
    for (int bit = 29; bit >= 0; bit--) {
        unsigned cand = ans | (1u << bit);
        if (feasible(a, b, n, cand, ka, kb))
            ans = cand;
    }
    return ans;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static unsigned a[100005], b[100005], ka[100005], kb[100005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%u", &a[i]);
//         for (int i = 0; i < n; i++)
//             scanf("%u", &b[i]);
//         printf("%u\n", solver(a, b, n, ka, kb));
//     }
//     return 0;
// }
