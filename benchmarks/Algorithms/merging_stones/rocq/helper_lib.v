Require Export PVbench.Algorithms.merging_stones.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib AUXLib.MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Arguments Zlength {A}.

Definition StoneIntervalMin
    (stones : list Z) (left right answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost => StoneMergePlan stones left right cost)
    (fun cost => cost)
    answer.

(* Progress predicates describe mathematical facts; execution bounds and
   list dimensions are separate premises in annotations and helper lemmas. *)
Definition StonePrefixProgress (stones prefix : list Z) (done : Z) : Prop :=
  forall k, 0 <= k <= done ->
    Znth k prefix 0 = sum (sublist 0 k stones).

Definition StonePrefixDone (stones prefix : list Z) (n : Z) : Prop :=
  StonePrefixProgress stones prefix n.

Definition StoneZeroRows (table : list (list Z)) (row : Z) : Prop :=
  Forall (Forall (eq 0)) (sublist 0 row table).

Definition StoneZeroProgress (table : list (list Z)) (row col : Z) : Prop :=
  StoneZeroRows table row /\
  Forall (eq 0) (sublist 0 col (Znth row table [])).

Definition StoneLenDone
    (stones : list Z) (table : list (list Z)) (n len : Z) : Prop :=
  forall l left right,
    1 <= l < len -> right = left + l - 1 ->
    0 <= left -> left + l <= n ->
    StoneIntervalMin stones left right (Znth right (Znth left table []) 0).

Definition StoneLeftProgress
    (stones : list Z) (table : list (list Z)) (n len left : Z) : Prop :=
  StoneLenDone stones table n len /\
  forall done_left right,
    0 <= done_left < left -> right = done_left + len - 1 ->
    done_left + len <= n ->
    StoneIntervalMin stones done_left right
      (Znth right (Znth done_left table []) 0).

Definition StoneSplitCandidate
    (stones : list Z) (table : list (list Z))
    (left right split candidate : Z) : Prop :=
  left <= split < right /\ right < Zlength stones /\
  candidate = Znth split (Znth left table []) 0 +
    Znth right (Znth (split + 1) table []) 0 +
    sum (sublist left (right + 1) stones).

Definition StoneSplitProgress
    (stones : list Z) (table : list (list Z))
    (n len left split best : Z) : Prop :=
  StoneLeftProgress stones table n len left /\
  ((split = left /\ best = 1000000) \/
   (left < split /\
    min_value_of_subset Z.le
      (fun candidate => exists k, left <= k < split /\
        StoneSplitCandidate stones table left (left + len - 1) k candidate)
      (fun candidate => candidate) best)).
