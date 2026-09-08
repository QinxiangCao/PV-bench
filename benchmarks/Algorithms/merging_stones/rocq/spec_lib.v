Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StoneMassesBounded (stones : list Z) (n : Z) : Prop :=
  Zlength stones = n /\
  forall i, 0 <= i < n -> 1 <= Znth i stones 0 <= 1000.
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
Definition StoneIntervalMin
    (stones : list Z) (left right answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost => StoneMergePlan stones left right cost)
    (fun cost => cost)
    answer.
Definition StoneMinimumCost
    (stones : list Z) (n answer : Z) : Prop :=
  Zlength stones = n /\ StoneIntervalMin stones 0 (n - 1) answer.
Definition StonePrefixProgress
    (stones prefix : list Z) (n done : Z) : Prop :=
  Zlength stones = n /\
  Zlength prefix = done + 1 /\
  0 <= done <= n /\
  forall k, 0 <= k <= done ->
    Znth k prefix 0 = sum (sublist 0 k stones).
Definition StonePrefixDone
    (stones prefix : list Z) (n : Z) : Prop :=
  StonePrefixProgress stones prefix n n.
Definition StoneTableShape (table : list (list Z)) (n : Z) : Prop :=
  Zlength table = n /\
  forall row, 0 <= row < n -> Zlength (Znth row table []) = n.
Definition StoneLenDone
    (stones : list Z) (table : list (list Z)) (n len : Z) : Prop :=
  Zlength stones = n /\
  StoneTableShape table n /\
  1 <= len /\
  forall l left right,
    1 <= l < len ->
    right = left + l - 1 ->
    0 <= left ->
    left + l <= n ->
    StoneIntervalMin stones left right
      (Znth right (Znth left table []) 0).
