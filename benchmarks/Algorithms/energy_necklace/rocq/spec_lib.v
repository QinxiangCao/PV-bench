Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.MonotonicList.

Definition EnergyValsDuplicated (beads vals : list Z) (n : Z) : Prop :=
  0 <= n /\
  Zlength beads = n /\
  Zlength vals = 2 * n /\
  (forall i, 0 <= i < n -> Znth i vals 0 = Znth i beads 0) /\
  (forall i, 0 <= i < n -> Znth (n + i) vals 0 = Znth i beads 0).

Inductive EnergyIntervalPlan (vals : list Z) : Z -> Z -> Z -> Prop :=
  | EnergyIntervalPlan_single :
      forall left,
        0 <= left ->
        left + 1 < Zlength vals ->
        EnergyIntervalPlan vals left left 0
  | EnergyIntervalPlan_merge :
      forall left split right e_left e_right,
        0 <= left ->
        left <= split < right ->
        right + 1 < Zlength vals ->
        EnergyIntervalPlan vals left split e_left ->
        EnergyIntervalPlan vals (split + 1) right e_right ->
        EnergyIntervalPlan vals left right
          (e_left + e_right +
             Znth left vals 0 * Znth (split + 1) vals 0 *
             Znth (right + 1) vals 0).

Definition EnergyIntervalBest
    (vals : list Z) (left right answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun energy => EnergyIntervalPlan vals left right energy)
    (fun energy => energy)
    answer.

Definition EnergyRotationBest
    (beads : list Z) (n start answer : Z) : Prop :=
  exists vals,
    EnergyValsDuplicated beads vals n /\
    0 <= start < n /\
    EnergyIntervalBest vals start (start + n - 1) answer.

Definition EnergyNecklaceAnswer
    (beads : list Z) (n answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun energy =>
       exists start, 0 <= start < n /\ EnergyRotationBest beads n start energy)
    (fun energy => energy)
    answer.
