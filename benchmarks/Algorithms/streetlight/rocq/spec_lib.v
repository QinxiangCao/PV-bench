From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive StreetlightPlan
    (positions powers : list Z) (start : Z) :
    Z -> Z -> Z -> Z -> Prop :=
  | StreetlightPlan_start :
      0 <= start < Zlength positions ->
      Zlength powers = Zlength positions ->
      StreetlightPlan positions powers start start start start 0
  | StreetlightPlan_extend_left :
      forall left right endpoint cost,
        0 <= left ->
        left < start <= right ->
        right < Zlength positions ->
        StreetlightPlan positions powers start
          (left + 1) right endpoint cost ->
        StreetlightPlan positions powers start left right left
          (cost +
           (Znth endpoint positions 0 - Znth left positions 0) *
           (sum powers - sum (sublist (left + 1) (right + 1) powers)))
  | StreetlightPlan_extend_right :
      forall left right endpoint cost,
        0 <= left ->
        left <= start < right ->
        right < Zlength positions ->
        StreetlightPlan positions powers start
          left (right - 1) endpoint cost ->
        StreetlightPlan positions powers start left right right
          (cost +
           (Znth right positions 0 - Znth endpoint positions 0) *
           (sum powers - sum (sublist left right powers))).
Definition StreetlightCompletePlan
    (positions powers : list Z) (start cost : Z) : Prop :=
  exists endpoint,
    StreetlightPlan positions powers start
      0 (Zlength positions - 1) endpoint cost.
Definition StreetlightMinimumEnergy
    (positions powers : list Z) (start answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost => StreetlightCompletePlan positions powers start cost)
    (fun cost => cost)
    answer.
