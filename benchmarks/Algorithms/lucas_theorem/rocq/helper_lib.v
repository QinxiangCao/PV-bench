Require Export PVbench.Algorithms.lucas_theorem.rocq.spec_lib.
From Coq Require Import ZArith List.
From SumLib Require Import ZRange.
Import ListNotations.
Local Open Scope Z_scope.
(** The declaration and verified implementation share the same result predicate. *)
Require Export PVbench.Algorithms.modular_power.rocq.helper_lib.
From Coq Require Import Lia Ring.
From Coq Require Import Znumtheory PeanoNat Permutation Lia.
From Coq Require Import Lia Arith.Factorial setoid_ring.ArithRing.
From Coq Require Import ZArith.Znumtheory ZArith.Zquot.

Definition BinomialDigitResidue
    (upper lower p result : Z) : Prop :=
  result = LucasBinomialCoefficient upper lower mod p.

(** A finite mathematical product of [count] consecutive integers beginning
    at [start]. *)
Definition LucasRangeProduct (start count : Z) : Z :=
  fold_right Z.mul 1 (Zrange start (start + count)).

Definition DigitNumeratorPrefix
    (upper lower processed : Z) : Z :=
  LucasRangeProduct (upper - lower + 1) processed.

Definition DigitDenominatorPrefix (processed : Z) : Z :=
  LucasRangeProduct 1 processed.

(** The digit at [position] in a nonnegative integer's base-[p]
    representation. *)
Definition LucasDigit (value p : Z) (position : Z) : Z :=
  (value / p ^ position) mod p.

(** Product, modulo [p], of the first [digits] Lucas digit coefficients. *)
Definition LucasPrefixProduct
    (upper lower p : Z) (digits : Z) : Z :=
  fold_right Z.mul 1
    (map
      (fun position =>
        LucasBinomialCoefficient
          (LucasDigit upper p position)
          (LucasDigit lower p position) mod p)
      (Zrange 0 digits)) mod p.

(** Internal mathematical state for the multiplicative digit helper. *)
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
  exists processed : Z,
    0 <= processed /\
    current_upper =
      original_upper / p ^ processed /\
    current_lower =
      original_lower / p ^ processed /\
    result =
      LucasPrefixProduct original_upper original_lower p processed /\
    LucasBinomialCoefficient original_upper original_lower mod p =
      (result *
       LucasBinomialCoefficient current_upper current_lower) mod p.
