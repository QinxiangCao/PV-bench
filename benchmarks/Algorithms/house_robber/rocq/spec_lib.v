Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* These bounds define the mathematical candidate domain: indices in a
   prefix of the input. Machine limits and input value bounds belong in C. *)
Definition NonAdjacentIndexList (limit : Z) (picks : list Z) : Prop :=
  0 <= limit /\
  NoDup picks /\
  Forall (fun i => 0 <= i < limit) picks /\
  (forall i j,
      In i picks ->
      In j picks ->
      i <> j ->
      2 <= Z.abs (i - j)).

Definition RobPlanValue (l : list Z) (picks : list Z) : Z :=
  sum (map (fun i => Znth i l 0) picks).

Definition RobPrefixValue (l : list Z) (len value : Z) : Prop :=
  exists picks,
    0 <= len <= Zlength l /\
    NonAdjacentIndexList len picks /\
    value = RobPlanValue l picks.

Definition HouseRobberAnswer (l : list Z) (answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun value => RobPrefixValue l (Zlength l) value)
    (fun value => value)
    answer.
