Require Export PVbench.Algorithms.zero_one_knapsack.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
(* Helper imports migrated from zero_one_knapsack__vc_proving_subagent_merged_proof_manual.v. *)
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Definition KnapsackCellCorrect
    (weights values : list Z) (row col value : Z) : Prop :=
  KnapsackMaxValue weights values row col value.

Definition KnapsackCellIndex (capacity row col : Z) : Z :=
  row * (capacity + 1) + col.

Definition KnapsackTablePrefix
    (weights values : list Z) (capacity : Z) (dp : list Z)
    (written : Z) : Prop :=
  forall row col,
    0 <= row ->
    0 <= col <= capacity ->
    0 <= KnapsackCellIndex capacity row col < written ->
    KnapsackCellCorrect weights values row col
      (Znth (KnapsackCellIndex capacity row col) dp 0).

Definition KnapsackRowsDone
    (weights values : list Z) (capacity : Z) (dp : list Z)
    (rows_done : Z) : Prop :=
  KnapsackTablePrefix weights values capacity dp
    (rows_done * (capacity + 1)).

Definition KnapsackRowProgress
    (weights values : list Z) (capacity : Z) (dp : list Z)
    (row col : Z) : Prop :=
  KnapsackTablePrefix weights values capacity dp
    (row * (capacity + 1) + col).
