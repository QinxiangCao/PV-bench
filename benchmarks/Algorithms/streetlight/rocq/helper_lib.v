Require Export PVbench.Algorithms.streetlight.rocq.spec_lib.
From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

From Coq Require Import Lia.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.

Require Import Coq.Relations.Relation_Operators.
Require Import AUXLib.MonotonicList.
Definition StreetlightState : Type := (Z * Z * Z * Z)%type.
Definition StreetlightStep (positions powers : list Z) (start : Z)
    (before after : StreetlightState) : Prop :=
  exists left right endpoint cost,
    (0 <= left /\ left < start <= right /\ right < Zlength positions /\
     before = (left + 1, right, endpoint, cost) /\
     after = (left, right, left, cost +
       (Znth endpoint positions 0 - Znth left positions 0) *
       (sum powers - sum (sublist (left + 1) (right + 1) powers)))) \/
    (0 <= left /\ left <= start < right /\ right < Zlength positions /\
     before = (left, right - 1, endpoint, cost) /\
     after = (left, right, right, cost +
       (Znth right positions 0 - Znth endpoint positions 0) *
       (sum powers - sum (sublist left right powers)))).
Definition StreetlightPlan (positions powers : list Z) (start left right endpoint cost : Z) : Prop :=
  0 <= start < Zlength positions /\
  Relation_Operators.clos_refl_trans StreetlightState
    (StreetlightStep positions powers start)
    (start,start,start,0) (left,right,endpoint,cost).
Definition StreetlightCompletePlan (positions powers : list Z) (start cost : Z) : Prop :=
  exists endpoint, StreetlightPlan positions powers start 0 (Zlength positions - 1) endpoint cost.
Definition StreetlightMinimumEnergy (positions powers : list Z) (start answer : Z) : Prop :=
  min_value_of_subset Z.le (StreetlightCompletePlan positions powers start) (fun cost : Z => cost) answer.

Definition StreetlightRowLength (row : list Z) : Z := Zlength row.
Definition StreetlightPrefixProgress (powers prefix : list Z) (done : Z) : Prop :=
  forall k, 0 <= k <= done -> Znth k prefix 0 = sum (sublist 0 k powers).
Definition StreetlightInfRows (table : list (list Z)) (_n rows_done : Z) : Prop :=
  Forall (Forall (eq 2147483647)) (sublist 0 rows_done table).
Definition StreetlightInfProgress (table : list (list Z)) (n row next_col : Z) : Prop :=
  StreetlightInfRows table n row /\
  Forall (eq 2147483647) (sublist 0 next_col (Znth row table [])).
Definition StreetlightEndpointMinimum
    (positions powers : list Z) (start left right endpoint answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost =>
       StreetlightPlan positions powers start left right endpoint cost)
    (fun cost => cost)
    answer.

Definition StreetlightLeftEntryCorrect
    (positions powers : list Z) (start left right value : Z) : Prop :=
  (left = start /\ right = start /\ value = 0) \/
  (left < start /\
   StreetlightEndpointMinimum
     positions powers start left right left value) \/
  (left = start /\ start < right /\ value = 2147483647).

Definition StreetlightRightEntryCorrect
    (positions powers : list Z) (start left right value : Z) : Prop :=
  (left = start /\ right = start /\ value = 0) \/
  (start < right /\
   StreetlightEndpointMinimum
     positions powers start left right right value) \/
  (left < start /\ right = start /\ value = 2147483647).

Definition StreetlightIntervalCorrect
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (start left right : Z) : Prop :=
  StreetlightLeftEntryCorrect positions powers start left right
    (Znth right (Znth left left_table []) 0) /\
  StreetlightRightEntryCorrect positions powers start left right
    (Znth right (Znth left right_table []) 0).

Definition StreetlightLengthsDone (positions powers : list Z)
    (left_table right_table : list (list Z)) (n start next_len : Z) : Prop :=
  forall len left right, 1 <= len < next_len -> right = left + len - 1 ->
    0 <= left -> right < n -> left <= start <= right ->
    StreetlightIntervalCorrect positions powers left_table right_table start left right.
Definition StreetlightLeftProgress
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (n start len next_left : Z) : Prop :=
  StreetlightLengthsDone
    positions powers left_table right_table n start len /\
  forall left right,
    0 <= left < next_left ->
    right = left + len - 1 ->
    right < n ->
    left <= start <= right ->
    StreetlightIntervalCorrect
      positions powers left_table right_table start left right.

Definition StreetlightLeftEndpointReady
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (n start len left : Z) : Prop :=
  StreetlightLeftProgress
    positions powers left_table right_table n start len left /\
  let right := left + len - 1 in
  StreetlightLeftEntryCorrect positions powers start left right
    (Znth right (Znth left left_table []) 0).

Definition StreetlightFinalCandidates
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (start left_answer right_answer : Z) : Prop :=
  let right := Zlength positions - 1 in
  StreetlightLeftEntryCorrect positions powers start 0 right left_answer /\
  StreetlightRightEntryCorrect positions powers start 0 right right_answer /\
  StreetlightMinimumEnergy
    positions powers start (Z.min left_answer right_answer).

From SumLib Require Import ZRange.
Require Import Coq.Sorting.Permutation.
