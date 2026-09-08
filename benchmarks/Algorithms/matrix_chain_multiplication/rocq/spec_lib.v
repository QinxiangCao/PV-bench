From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MatrixChainDimensionsBounded
    (dimensions : list Z) (matrix_count : Z) : Prop :=
  Zlength dimensions = matrix_count + 1 /\
  forall i, 0 <= i <= matrix_count ->
    1 <= Znth i dimensions 0 <= 100.
Inductive MatrixChainPlan
    (dimensions : list Z) : Z -> Z -> Z -> Prop :=
  | MatrixChainPlan_single :
      forall left,
        0 <= left ->
        left + 1 < Zlength dimensions ->
        MatrixChainPlan dimensions left left 0
  | MatrixChainPlan_join :
      forall left split right left_cost right_cost,
        0 <= left ->
        left <= split < right ->
        right + 1 < Zlength dimensions ->
        MatrixChainPlan dimensions left split left_cost ->
        MatrixChainPlan dimensions (split + 1) right right_cost ->
        MatrixChainPlan dimensions left right
          (left_cost + right_cost +
           Znth left dimensions 0 *
           Znth (split + 1) dimensions 0 *
           Znth (right + 1) dimensions 0).
Definition MatrixChainIntervalMinimum
    (dimensions : list Z) (left right answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun scalar_cost =>
       MatrixChainPlan dimensions left right scalar_cost)
    (fun scalar_cost => scalar_cost)
    answer.
Definition MatrixChainMinimumCost
    (dimensions : list Z) (matrix_count answer : Z) : Prop :=
  Zlength dimensions = matrix_count + 1 /\
  MatrixChainIntervalMinimum dimensions 0 (matrix_count - 1) answer.
Definition MatrixChainTableResult
    (dimensions table : list Z) (matrix_count : Z) : Prop :=
  Zlength table = matrix_count * matrix_count /\
  forall left right,
    0 <= left /\ left <= right /\ right < matrix_count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * matrix_count + right) table 0).
