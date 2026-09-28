Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib AUXLib.MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Arguments Zlength {A}.

Inductive StoneMergePlan (stones : list Z) : Z -> Z -> Z -> Prop :=
  | StoneMergePlan_single :
      forall left,
        0 <= left < Zlength stones ->
        StoneMergePlan stones left left 0
  | StoneMergePlan_join :
      forall left split right left_cost right_cost,
        0 <= left ->
        left <= split < right ->
        right < Zlength stones ->
        StoneMergePlan stones left split left_cost ->
        StoneMergePlan stones (split + 1) right right_cost ->
        StoneMergePlan stones left right
          (left_cost + right_cost + sum (sublist left (right + 1) stones)).

(* The public result only describes the least cost among adjacent merge trees. *)
Definition StoneMinimumCost (stones : list Z) (answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost => StoneMergePlan stones 0 (Zlength stones - 1) cost)
    (fun cost => cost) answer.
