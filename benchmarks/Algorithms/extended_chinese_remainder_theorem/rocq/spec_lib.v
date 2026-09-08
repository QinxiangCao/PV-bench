From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.

Definition CRTLCMPrefix (moduli : list Z) (count : Z) : Z :=
  fold_left Z.lcm (firstn (Z.to_nat count) moduli) 1.
Definition CRTCongruent (value residue modulus : Z) : Prop :=
  exists quotient, value = residue + modulus * quotient.
Definition CRTAllCongruences
    (residues moduli : list Z) (count value : Z) : Prop :=
  forall index,
    0 <= index < count ->
    CRTCongruent value (Znth index residues 0) (Znth index moduli 0).
Definition ExtendedCRTInputs
    (residues moduli : list Z) (n : Z) : Prop :=
  1 <= n /\
  Zlength residues = n /\
  Zlength moduli = n /\
  forall index,
    0 <= index < n ->
    0 < Znth index moduli 0 <= 2147483647 /\
    0 <= Znth index residues 0 < Znth index moduli 0.
Definition ExtendedCRTSystemCompatible
    (residues moduli : list Z) (n : Z) : Prop :=
  exists solution, CRTAllCongruences residues moduli n solution.
Definition ExtendedCRTIntSafe (moduli : list Z) (n : Z) : Prop :=
  (forall count,
     1 <= count <= n ->
     0 < CRTLCMPrefix moduli count <= 2147483647) /\
  (forall index,
     1 <= index < n ->
     2 * Z.quot
       (Znth index moduli 0)
       (Z.gcd (CRTLCMPrefix moduli index) (Znth index moduli 0))
       <= 2147483647).
Definition ExtendedCRTSystemResult
    (residues moduli : list Z)
    (n result combined_modulus : Z) : Prop :=
  combined_modulus = CRTLCMPrefix moduli n /\
  0 <= result < combined_modulus /\
  CRTAllCongruences residues moduli n result.
