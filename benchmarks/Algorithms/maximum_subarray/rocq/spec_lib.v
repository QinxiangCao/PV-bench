Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MaxSubarraySumPrefix (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun p : Z * Z =>
       let '(lo, hi) := p in
       0 <= lo /\ lo < hi /\ hi <= i)
    (fun p : Z * Z =>
       let '(lo, hi) := p in
       sum (sublist lo hi l))
    ans.

Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
Import SetsNotation.
