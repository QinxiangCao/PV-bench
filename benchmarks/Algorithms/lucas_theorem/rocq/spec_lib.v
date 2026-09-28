From Coq Require Import ZArith List.
From SumLib Require Import ZRange.
Import ListNotations.
Local Open Scope Z_scope.
(** The declaration and verified implementation share the same result predicate. *)
Require Export PVbench.Algorithms.modular_power.rocq.spec_lib.
From Coq Require Import Lia Ring.
From Coq Require Import Znumtheory PeanoNat Permutation Lia.
From Coq Require Import Lia Arith.Factorial setoid_ring.ArithRing.
From Coq Require Import ZArith.Znumtheory ZArith.Zquot.

(** A positive integer is prime when it has no nontrivial divisor.  This
    case-local formulation keeps the public annotation surface independent of
    proof-only number-theory imports. *)
Definition PrimeForLucas (p : Z) : Prop :=
  2 <= p /\
  forall divisor,
    2 <= divisor < p ->
    p mod divisor <> 0.

(** Existing Pascal/factorial proof foundation.  Its nat implementation is
    retained for the proved number-theory helpers below; the public coefficient,
    digit, product and annotation interfaces all use Z. *)
Fixpoint LucasNatBinomial (upper lower : nat) : nat :=
  match upper, lower with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S upper', S lower' =>
      (LucasNatBinomial upper' lower' +
       LucasNatBinomial upper' (S lower'))%nat
  end.

Definition LucasBinomialCoefficient (upper lower : Z) : Z :=
  Z.of_nat
    (LucasNatBinomial (Z.to_nat upper) (Z.to_nat lower)).

Definition LucasBinomialResidue
    (n m p result : Z) : Prop :=
  result = LucasBinomialCoefficient (n + m) n mod p.
