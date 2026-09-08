Require Import PVbench.Algorithms.lucas_theorem.rocq.spec_lib.

From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition BinomialDigitResidue
    (upper lower p result : Z) : Prop :=
  result = LucasBinomialCoefficient upper lower mod p.
Definition DigitProductProgress
    (upper lower p next numerator denominator : Z) : Prop :=
  numerator = DigitNumeratorPrefix upper lower (next - 1) mod p /\
  denominator = DigitDenominatorPrefix (next - 1) mod p.

(** Internal mathematical state for Lucas digit decomposition.  The
    existential position is a mathematical digit coordinate, not a mirror of
    a C loop counter. *)
Definition LucasProgress
    (original_upper original_lower p
     current_upper current_lower result : Z) : Prop :=
  exists processed : nat,
    current_upper =
      original_upper / p ^ Z.of_nat processed /\
    current_lower =
      original_lower / p ^ Z.of_nat processed /\
    result =
      LucasPrefixProduct original_upper original_lower p processed /\
    LucasBinomialCoefficient original_upper original_lower mod p =
      (result *
       LucasBinomialCoefficient current_upper current_lower) mod p.
