Require Export PVbench.Algorithms.energy_necklace.rocq.spec_lib.
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

Definition EnergyCellIndex (width left right : Z) : Z :=
  left * width + right.

Definition EnergySplitCandidate
    (vals dp : list Z) (width left right split candidate : Z) : Prop :=
  left <= split < right /\
  right + 1 < Zlength vals /\
  candidate =
    Znth (EnergyCellIndex width left split) dp 0 +
    Znth (EnergyCellIndex width (split + 1) right) dp 0 +
    Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0.

(** Public progress predicates contain only mathematical table facts.  The
    original helper lemmas above remain available for proof reuse. *)
Definition EnergyLengthsComplete (vals dp : list Z) (width len : Z) : Prop :=
  forall l left right idx,
    1 <= l < len -> right = left + l - 1 ->
    idx = EnergyCellIndex width left right -> 0 <= left ->
    left + l < Zlength vals ->
    EnergyIntervalBest vals left right (Znth idx dp 0).

Definition EnergyLeftComplete (vals dp : list Z) (width len left : Z) : Prop :=
  forall done_left right idx,
    0 <= done_left < left -> right = done_left + len - 1 ->
    idx = EnergyCellIndex width done_left right ->
    done_left + len < Zlength vals ->
    EnergyIntervalBest vals done_left right (Znth idx dp 0).

Definition EnergySplitBest (vals dp : list Z) (width len left split best : Z) : Prop :=
  (split = left /\ best = 0) \/
  (left < split /\ max_value_of_subset Z.le
    (fun candidate => exists k, left <= k < split /\
      EnergySplitCandidate vals dp width left (left + len - 1) k candidate)
    (fun candidate => candidate) best).

Definition EnergyAnswerBest (vals : list Z) (n start answer : Z) : Prop :=
  (start = 0 /\ answer = 0) \/
  (0 < start /\ max_value_of_subset Z.le
    (fun value => exists s, 0 <= s < start /\
      EnergyIntervalBest vals s (s + n - 1) value)
    (fun value => value) answer).
