Require Import PVbench.Algorithms.matrix_chain_multiplication.rocq.spec_lib.

From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MatrixChainZeroPrefix (table : list Z) (done : Z) : Prop :=
  Zlength table = done /\
  forall index, 0 <= index < done -> Znth index table 0 = 0.
Definition MatrixChainTableValuesBounded (table : list Z) : Prop :=
  forall index, 0 <= index < Zlength table ->
    0 <= Znth index table 0 <= 7000000.
Definition MatrixChainLengthsDone
    (dimensions table : list Z) (matrix_count next_length : Z) : Prop :=
  1 <= next_length /\
  forall length left right,
    1 <= length < next_length ->
    right = left + length - 1 ->
    0 <= left ->
    left + length <= matrix_count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * matrix_count + right) table 0).
Definition MatrixChainLeftProgress
    (dimensions table : list Z)
    (matrix_count length next_left : Z) : Prop :=
  MatrixChainLengthsDone dimensions table matrix_count length /\
  forall left right,
    0 <= left < next_left ->
    right = left + length - 1 ->
    left + length <= matrix_count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * matrix_count + right) table 0).
Definition MatrixChainSplitCandidate
    (dimensions table : list Z)
    (width left right split candidate : Z) : Prop :=
  candidate =
    Znth (left * width + split) table 0 +
    Znth ((split + 1) * width + right) table 0 +
    Znth left dimensions 0 *
    Znth (split + 1) dimensions 0 *
    Znth (right + 1) dimensions 0.
Definition MatrixChainSplitProgress
    (dimensions table : list Z)
    (matrix_count width length left next_split best : Z) : Prop :=
  MatrixChainLeftProgress dimensions table matrix_count length left /\
  let right := left + length - 1 in
  min_value_of_subset Z.le
    (fun candidate =>
       exists split,
         left <= split < next_split /\
         MatrixChainSplitCandidate
           dimensions table width left right split candidate)
    (fun candidate => candidate)
    best.
