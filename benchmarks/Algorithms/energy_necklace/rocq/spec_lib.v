Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition EnergyValsDuplicated (beads vals : list Z) (n : Z) : Prop :=
  0 <= n /\
  Zlength beads = n /\
  Zlength vals = 2 * n /\
  (forall i, 0 <= i < n -> Znth i vals 0 = Znth i beads 0) /\
  (forall i, 0 <= i < n -> Znth (n + i) vals 0 = Znth i beads 0).
Definition EnergyLabelsBounded (beads : list Z) (n : Z) : Prop :=
  Zlength beads = n /\
  forall i, 0 <= i < n -> 1 <= Znth i beads 0 <= 1000.
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
Definition EnergyCellIndex (width left right : Z) : Z :=
  left * width + right.
Definition EnergyLenDone
    (vals dp : list Z) (total width len : Z) : Prop :=
  0 <= total /\
  width = total /\
  Zlength vals = total /\
  Zlength dp = total * width /\
  1 <= len /\
  (forall l left right idx,
     1 <= l < len ->
     right = left + l - 1 ->
     idx = EnergyCellIndex width left right ->
     0 <= left ->
     left + l < Zlength vals ->
     EnergyIntervalBest vals left right (Znth idx dp 0)).
Definition EnergySplitArithmeticBounded
    (vals dp : list Z) (width left right split bound : Z) : Prop :=
  let left_value := Znth (EnergyCellIndex width left split) dp 0 in
  let right_value := Znth (EnergyCellIndex width (split + 1) right) dp 0 in
  let gain :=
    Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0 in
  0 <= left_value <= bound /\
  0 <= right_value <= bound /\
  0 <= gain <= bound /\
  0 <= left_value + right_value <= bound /\
  0 <= left_value + right_value + gain <= bound.
Definition EnergyComputationBounded
    (beads : list Z) (n bound : Z) : Prop :=
  0 <= bound /\
  (forall vals dp total width len left right split,
     EnergyValsDuplicated beads vals n ->
     total = 2 * n ->
     width = total ->
     2 <= len <= n ->
     0 <= left < total - len ->
     right = left + len - 1 ->
     left <= split < right ->
     Zlength dp = total * width ->
     EnergyLenDone vals dp total width len ->
     EnergySplitArithmeticBounded vals dp width left right split bound) /\
  (forall vals left right answer,
     EnergyValsDuplicated beads vals n ->
     0 <= left ->
     left <= right ->
     right + 1 < Zlength vals ->
     EnergyIntervalBest vals left right answer ->
     0 <= answer <= bound) /\
  (forall vals dp total width start,
     EnergyValsDuplicated beads vals n ->
     total = 2 * n ->
     width = total ->
     0 <= start < n ->
     Zlength dp = total * width ->
     EnergyLenDone vals dp total width (n + 1) ->
     0 <= Znth (EnergyCellIndex width start (start + n - 1)) dp 0 <= bound).

Require Import Coq.micromega.Psatz.
