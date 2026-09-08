Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition Power2 (j : Z) : Z := Z.pow 2 j.

(** Program-safety and data-representation predicates.  These predicates do
    not claim that any sparse-table cell contains the right answer. *)
Definition RMQSizeSafe (n K : Z) : Prop :=
  1 <= n /\
  n <= 100000 /\
  1 <= K /\
  K <= 30 /\
  n * K <= 1000000 /\
  n < Power2 K.
Definition STTableShape (st_ls : list Z) (K n : Z) : Prop :=
  Zlength st_ls = n * K.
Definition STBuiltBeforeLevelBounds (K level : Z) : Prop :=
  0 <= level /\ level <= K.
Definition RangeMaxValue (l : list Z) (lo hi ans : Z) : Prop :=
  0 <= lo /\
  lo < hi /\
  hi <= Zlength l /\
  max_value_of_subset Z.le
    (fun k => lo <= k /\ k < hi)
    (fun k => Znth k l 0)
    ans.
Definition STCellRangeMax
    (l st_ls : list Z) (K i j : Z) : Prop :=
  RangeMaxValue l i (i + Power2 j) (Znth (i * K + j) st_ls 0).
Definition STBuiltBeforeLevel
    (l st_ls : list Z) (K n level : Z) : Prop :=
  forall i j,
    0 <= i /\ 0 <= j /\ j < level /\ i + Power2 j <= n ->
    STCellRangeMax l st_ls K i j.
Definition STBuilt (l st_ls : list Z) (K n : Z) : Prop :=
  STBuiltBeforeLevel l st_ls K n K.
Definition QueryIntervalBounds (n left right : Z) : Prop :=
  0 <= left /\ left <= right /\ right < n.
