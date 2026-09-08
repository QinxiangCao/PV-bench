Require Import PVbench.Algorithms.streetlight.rocq.spec_lib.

From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StreetlightTableShape
    (table : list (list Z)) (n : Z) : Prop :=
  Zlength table = n /\
  forall row, 0 <= row < n -> Zlength (Znth row table []) = n.
Definition StreetlightPrefixProgress
    (powers prefix : list Z) (done : Z) : Prop :=
  Zlength prefix = done + 1 /\
  forall k, 0 <= k <= done ->
    Znth k prefix 0 = sum (sublist 0 k powers).
Definition StreetlightInfRows
    (table : list (list Z)) (n rows_done : Z) : Prop :=
  StreetlightTableShape table n /\
  forall row col,
    0 <= row < rows_done ->
    0 <= col < n ->
    Znth col (Znth row table []) 0 = 2147483647.
Definition StreetlightInfProgress
    (table : list (list Z)) (n row next_col : Z) : Prop :=
  StreetlightInfRows table n row /\
  forall col,
    0 <= col < next_col ->
    Znth col (Znth row table []) 0 = 2147483647.
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
Definition StreetlightLengthsDone
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (n start next_len : Z) : Prop :=
  StreetlightTableShape left_table n /\
  StreetlightTableShape right_table n /\
  forall len left right,
    1 <= len < next_len ->
    right = left + len - 1 ->
    0 <= left ->
    right < n ->
    left <= start <= right ->
    StreetlightIntervalCorrect
      positions powers left_table right_table start left right.
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
