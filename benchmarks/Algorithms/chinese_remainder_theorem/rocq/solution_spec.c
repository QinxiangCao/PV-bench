/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::lt : Z -> Z -> Prop)
 */
/*@ Extern Coq (CanonicalCRTSolution: list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (CRTProduct: list Z -> Z) */
/*@ Extern Coq (Zgcd: Z -> Z -> Z) */
/*@ Import Coq Require Import PVbench.Algorithms.chinese_remainder_theorem.rocq.spec_lib */

int exgcd(int a, int b, int *x, int *y)
;

int chinese_remainder_theorem(int n, int *remainders, int *moduli)
/*@ With (remainders_l moduli_l : list Z)
    Require
      n == Zlength(moduli_l) &&
      Zlength(remainders_l) == Zlength(moduli_l) &&
      1 <= Zlength(moduli_l) &&
      Forall(Z::le(1), moduli_l) &&
      Forall(Z::le(0), remainders_l) &&
      Forall2(Z::lt, remainders_l, moduli_l) &&
      (forall (j k: Z),
        (0 <= j && j < k && k < Zlength(moduli_l)) =>
        Zgcd(Znth(j, moduli_l, 0), Znth(k, moduli_l, 0)) == 1) &&
      1 <= CRTProduct(moduli_l) && CRTProduct(moduli_l) <= 46340 &&
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

        int term = (int)(((long long)coefficient * partial_product) % product);
        term = (term * remainders[i]) % product;
        if (term < 0) {
            term += product;
        }

        result = (result + term) % product;
    }

    return result;
}
