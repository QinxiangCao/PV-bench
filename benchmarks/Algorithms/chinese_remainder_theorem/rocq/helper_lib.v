Require Import PVbench.Algorithms.chinese_remainder_theorem.rocq.spec_lib.

From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

Definition CRTProcessedCongruences
    (remainders moduli : list Z) (processed result : Z) : Prop :=
  forall i,
    0 <= i < processed ->
    result mod Znth i moduli 0 = Znth i remainders 0.
