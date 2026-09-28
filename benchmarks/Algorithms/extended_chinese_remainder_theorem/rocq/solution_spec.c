/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::lt : Z -> Z -> Prop)
      (CRTLCMPrefix : list Z -> Z -> Z)
      (Zgcd : Z -> Z -> Z)
      (ExtendedCRTSystemCompatible : list Z -> list Z -> Z -> Prop)
      (ExtendedCRTSystemResult : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.extended_chinese_remainder_theorem.rocq.spec_lib */

/*@ Import Coq Require Import PVbench.Algorithms.extended_chinese_remainder_theorem.rocq.spec_lib */

int exgcd(int a, int b, int *x, int *y)
;

int modular_mul(int a, int b, int modulus)
;

int extended_chinese_remainder_theorem(int n,
                                      int *residues,
                                      int *moduli,
                                      int *combined_modulus)
/*@ With (residue_values modulus_values : list Z)
    Require
      1 <= n &&
      Forall(Z::lt(0), modulus_values) &&
      Forall(Z::ge(INT_MAX), modulus_values) &&
      Forall(Z::le(0), residue_values) &&
      Forall2(Z::lt, residue_values, modulus_values) &&
      (forall (count : Z), 1 <= count && count <= n =>
        CRTLCMPrefix(modulus_values, count) <= INT_MAX) &&
      (forall (index : Z), 1 <= index && index < n =>
        2 * (Znth(index, modulus_values, 0) /
          Zgcd(CRTLCMPrefix(modulus_values, index),
               Znth(index, modulus_values, 0))) <= INT_MAX) &&
      ExtendedCRTSystemCompatible(residue_values, modulus_values, n) &&
      IntArray::full(residues, n, residue_values) *
      IntArray::full(moduli, n, modulus_values) *
      has_int_permission(combined_modulus)
    Ensure
      ExtendedCRTSystemResult(residue_values, modulus_values, n,
                              __return, *combined_modulus) &&
      IntArray::full(residues, n, residue_values) *
      IntArray::full(moduli, n, modulus_values)
*/
{
    int answer = residues[0];
    int lcm = moduli[0];

    for (int i = 1; i < n; ++i) {
        int x;
        int y;
        int gcd = exgcd(lcm, moduli[i], &x, &y);
        int reduced_modulus = moduli[i] / gcd;

        x = modular_mul(x, (residues[i] - answer) / gcd, reduced_modulus);
        if (x < 0) {
            x += reduced_modulus;
        }

        answer = answer + x * lcm;
        lcm = lcm * reduced_modulus;
    }

    *combined_modulus = lcm;
    return answer;
}
