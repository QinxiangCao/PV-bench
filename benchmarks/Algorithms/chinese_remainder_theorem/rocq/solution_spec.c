/*
 * Chinese remainder theorem, using the verified exgcd interface.
 *
 * The moduli are expected to be positive and pairwise coprime.  Under that
 * assumption, the function returns the unique value in [0, product) that is
 * congruent to remainders[i] modulo moduli[i] for every 0 <= i < n.
 *
 * This verification example deliberately uses int throughout.  As requested,
 * choosing inputs whose intermediate products fit in int is left outside the
 * algorithmic presentation here.
 */

/*@ Extern Coq
      (CRTInputValid: list Z -> list Z -> Prop)
      (CRTMachineSafe: list Z -> list Z -> Prop)
      (CanonicalCRTSolution: list Z -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.chinese_remainder_theorem.rocq.spec_lib */

int exgcd(int a, int b, int *x, int *y)
;

int chinese_remainder_theorem(int n, int *remainders, int *moduli)
/*@ With (remainders_l moduli_l : list Z)
    Require
      n == Zlength(moduli_l) &&
      CRTInputValid(remainders_l, moduli_l) &&
      CRTMachineSafe(remainders_l, moduli_l) &&
      IntArray::full(remainders, n, remainders_l) *
      IntArray::full(moduli, n, moduli_l)
    Ensure
      CanonicalCRTSolution(remainders_l, moduli_l, __return) &&
      IntArray::full(remainders, n, remainders_l) *
      IntArray::full(moduli, n, moduli_l)
 */
{
    int product = 1;

    for (int i = 0; i < n; ++i) {
        product *= moduli[i];
    }

    int result = 0;

    for (int i = 0; i < n; ++i) {
        int partial_product = product / moduli[i];
        int coefficient;
        int unused;

        exgcd(partial_product, moduli[i], &coefficient, &unused);

        int term = (coefficient * partial_product) % product;
        term = (term * remainders[i]) % product;
        if (term < 0) {
            term += product;
        }

        result = (result + term) % product;
    }

    return result;
}
