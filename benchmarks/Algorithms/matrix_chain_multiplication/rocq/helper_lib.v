Require Export PVbench.Algorithms.matrix_chain_multiplication.rocq.spec_lib.
From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
From Coq Require Import Lia.

Definition MatrixChainSplitCandidate
    (dimensions table : list Z)
    (width left right split candidate : Z) : Prop :=
  candidate =
    Znth (left * width + split) table 0 +
    Znth ((split + 1) * width + right) table 0 +
    Znth left dimensions 0 *
    Znth (split + 1) dimensions 0 *
    Znth (right + 1) dimensions 0.

Definition MatrixChainLengthsComplete (dimensions table : list Z) (count next : Z) : Prop :=
  forall len left right, 1 <= len < next -> right = left + len - 1 ->
    0 <= left -> left + len <= count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * count + right) table 0).

Definition MatrixChainLeftComplete (dimensions table : list Z) (count len next : Z) : Prop :=
  MatrixChainLengthsComplete dimensions table count len /\
  forall left right, 0 <= left < next -> right = left + len - 1 ->
    left + len <= count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * count + right) table 0).

Definition MatrixChainSplitMinimum (dimensions table : list Z)
  (count width len left next best : Z) : Prop :=
  MatrixChainLeftComplete dimensions table count len left /\
  min_value_of_subset Z.le
    (fun candidate => exists split, left <= split < next /\
      MatrixChainSplitCandidate dimensions table width left (left + len - 1) split candidate)
    (fun candidate => candidate) best.
