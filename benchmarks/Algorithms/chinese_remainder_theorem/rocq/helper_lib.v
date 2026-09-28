Require Export PVbench.Algorithms.chinese_remainder_theorem.rocq.spec_lib.
From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

From Coq Require Import Lia Ring.
From Coq Require Import Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Lia.

Require Import AUXLib.MonotonicList.

Require Import SimpleC.SL.IntLib.



(** The public progress relation compares corresponding initialized equations. *)
Definition CRTConsistentPrefix
    (remainders moduli : list Z) (processed result : Z) : Prop :=
  Forall2 (fun remainder modulus => result mod modulus = remainder)
    (sublist 0 processed remainders) (sublist 0 processed moduli).


Definition CRTUnprocessedZero (moduli : list Z) (processed result : Z) : Prop :=
  Forall (fun modulus => Z.rem result modulus = 0)
    (sublist processed (Zlength moduli) moduli).
