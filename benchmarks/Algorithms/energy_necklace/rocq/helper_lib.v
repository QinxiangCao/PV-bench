Require Import PVbench.Algorithms.energy_necklace.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition EnergyZeroTable (dp : list Z) (total width : Z) : Prop :=
  0 <= total /\
  width = total /\
  Zlength dp = total * width /\
  forall idx, 0 <= idx < total * width -> Znth idx dp 0 = 0.
Definition EnergyLeftProgress
    (vals dp : list Z) (total width len left : Z) : Prop :=
  EnergyLenDone vals dp total width len /\
  2 <= len /\
  0 <= left /\
  (forall done_left right idx,
     0 <= done_left < left ->
     right = done_left + len - 1 ->
     idx = EnergyCellIndex width done_left right ->
     done_left + len < Zlength vals ->
     EnergyIntervalBest vals done_left right (Znth idx dp 0)).
Definition EnergySplitCandidate
    (vals dp : list Z) (width left right split candidate : Z) : Prop :=
  left <= split < right /\
  right + 1 < Zlength vals /\
  candidate =
    Znth (EnergyCellIndex width left split) dp 0 +
    Znth (EnergyCellIndex width (split + 1) right) dp 0 +
    Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0.
Definition EnergySplitProgress
    (vals dp : list Z) (total width len left split best : Z) : Prop :=
  EnergyLeftProgress vals dp total width len left /\
  let right := left + len - 1 in
  2 <= len /\
  0 <= left /\
  left + len <= total /\
  right = left + len - 1 /\
  left <= split <= right /\
  0 <= best <= 2100000000 /\
  ((split = left /\ best = 0) \/
   (left < split /\
    max_value_of_subset Z.le
      (fun candidate =>
         exists k,
           left <= k < split /\
           EnergySplitCandidate vals dp width left right k candidate)
      (fun candidate => candidate)
      best)).
Definition EnergyUpdatedCell
    (vals old_dp new_dp : list Z) (width left right value : Z) : Prop :=
  0 <= EnergyCellIndex width left right < Zlength old_dp /\
  new_dp = replace_Znth (EnergyCellIndex width left right) value old_dp /\
  EnergyIntervalBest vals left right value.
Definition EnergyAnswerProgress
    (beads vals dp : list Z) (n total width start answer : Z) : Prop :=
  EnergyValsDuplicated beads vals n /\
  Zlength dp = total * width /\
  width = total /\
  0 <= start <= n /\
  0 <= answer <= 2100000000 /\
  ((start = 0 /\ answer = 0) \/
   (0 < start /\
    max_value_of_subset Z.le
      (fun value =>
         exists s,
           0 <= s < start /\
           EnergyIntervalBest vals s (s + n - 1) value)
      (fun value => value)
      answer)).
