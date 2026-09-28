From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition RodCutPlan (rod_len : Z) (pieces : list Z) : Prop :=
  0 <= rod_len /\
  Forall (fun piece => 1 <= piece <= rod_len) pieces /\
  sum pieces = rod_len.

Definition RodCutPlanRevenue (price pieces : list Z) : Z :=
  sum (map (fun piece => Znth piece price 0) pieces).

Definition RodCutOptimalRevenue
    (price : list Z) (rod_len answer : Z) : Prop :=
  max_value_of_subset Z.le
    (RodCutPlan rod_len)
    (RodCutPlanRevenue price)
    answer.

From Coq Require Import Lia.
