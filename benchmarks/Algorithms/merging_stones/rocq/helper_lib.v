Require Import PVbench.Algorithms.merging_stones.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StoneZeroRows
    (table : list (list Z)) (n row : Z) : Prop :=
  StoneTableShape table n /\
  0 <= row <= n /\
  forall r c, 0 <= r < row -> 0 <= c < n ->
    Znth c (Znth r table []) 0 = 0.
Definition StoneZeroProgress
    (table : list (list Z)) (n row col : Z) : Prop :=
  StoneTableShape table n /\
  0 <= row < n /\
  0 <= col <= n /\
  (forall r c, 0 <= r < row -> 0 <= c < n ->
     Znth c (Znth r table []) 0 = 0) /\
  (forall c, 0 <= c < col ->
     Znth c (Znth row table []) 0 = 0).
Definition StoneLeftProgress
    (stones : list Z) (table : list (list Z))
    (n len left : Z) : Prop :=
  StoneLenDone stones table n len /\
  2 <= len <= n /\
  0 <= left <= n - len + 1 /\
  forall done_left right,
    0 <= done_left < left ->
    right = done_left + len - 1 ->
    done_left + len <= n ->
    StoneIntervalMin stones done_left right
      (Znth right (Znth done_left table []) 0).
Definition StoneSplitCandidate
    (stones : list Z) (table : list (list Z))
    (left right split candidate : Z) : Prop :=
  left <= split < right /\
  right < Zlength stones /\
  candidate =
    Znth split (Znth left table []) 0 +
    Znth right (Znth (split + 1) table []) 0 +
    sum (sublist left (right + 1) stones).
Definition StoneSplitProgress
    (stones : list Z) (table : list (list Z))
    (n len left split best : Z) : Prop :=
  StoneLeftProgress stones table n len left /\
  let right := left + len - 1 in
  left <= split <= right /\
  0 <= best <= 1000000 /\
  ((split = left /\ best = 1000000) \/
   (left < split /\
    min_value_of_subset Z.le
      (fun candidate =>
         exists k,
           left <= k < split /\
           StoneSplitCandidate stones table left right k candidate)
      (fun candidate => candidate)
      best)).
Definition StoneUpdatedCell
    (stones : list Z) (old_table new_table : list (list Z))
    (left right value : Z) : Prop :=
  0 <= left < Zlength old_table /\
  0 <= right < Zlength (Znth left old_table []) /\
  new_table =
    replace_Znth left
      (replace_Znth right value (Znth left old_table []))
      old_table /\
  StoneIntervalMin stones left right value.
