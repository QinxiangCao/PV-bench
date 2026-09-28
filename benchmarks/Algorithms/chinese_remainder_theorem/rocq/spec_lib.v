From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

(** The mathematical modulus of a CRT instance.  This is a property of the
    input sequence and is independent of either loop in the C implementation. *)
Definition CRTProduct (moduli : list Z) : Z :=
  fold_right Z.mul 1 moduli.

(** The public functional result: [answer] is the canonical representative
    modulo the product and satisfies every input congruence.  Pairwise
    coprimality in [CRTInputValid] makes this representative unique. *)
Definition CanonicalCRTSolution
    (remainders moduli : list Z) (answer : Z) : Prop :=
  0 <= answer < CRTProduct moduli /\
  Forall2 (fun remainder modulus => answer mod modulus = remainder)
    remainders moduli.

From Coq Require Import Lia Ring.
From Coq Require Import Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Lia.

Require Import AUXLib.MonotonicList.

Require Import SimpleC.SL.IntLib.
