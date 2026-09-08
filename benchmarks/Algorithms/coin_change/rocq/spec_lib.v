Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive ReachableAmount (coins : list Z) : Z -> Prop :=
  | ReachableAmount_zero :
      ReachableAmount coins 0
  | ReachableAmount_add :
      forall v c,
        ReachableAmount coins v ->
        In c coins ->
        0 < c ->
        ReachableAmount coins (v + c).
Definition MaxReachableAmount (coins : list Z) (amount ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun v => ReachableAmount coins v /\ 0 <= v /\ v <= amount)
    (fun v => v)
    ans.
Definition DpReachableTable (coins : list Z) (dp : list Z) (hi : Z) : Prop :=
  0 <= hi /\
  Zlength dp >= hi /\
  forall k, 0 <= k < hi -> (Znth k dp 0 <> 0 <-> ReachableAmount coins k).
