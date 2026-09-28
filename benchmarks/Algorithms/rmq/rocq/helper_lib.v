Require Export PVbench.Algorithms.rmq.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
(* Helper imports migrated from rmq__vc_proving_subagent_merged_proof_manual.v. *)
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Definition STBasePrefix
    (l st_ls : list Z) (K n upto : Z) : Prop :=
  forall i, 0 <= i < upto -> STCellRangeMax l st_ls K i 0.

Definition STLevelPrefix
    (l st_ls : list Z) (K n j upto : Z) : Prop :=
  forall i,
    0 <= i /\ i < upto /\ i + Power2 j <= n ->
    STCellRangeMax l st_ls K i j.
