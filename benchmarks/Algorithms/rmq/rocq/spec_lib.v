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

Definition Power2 (j : Z) : Z := Z.pow 2 j.

(** The maximum of actual list elements whose indices lie in [lo, hi).
    Candidate-domain guards exclude negative/default reads; input validity and
    machine bounds belong to the C contract. *)
Definition RangeMaxValue (l : list Z) (lo hi ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun k => lo <= k < hi /\ 0 <= k < Zlength l)
    (fun k => Znth k l 0)
    ans.

Definition STCellRangeMax
    (l st_ls : list Z) (K i j : Z) : Prop :=
  RangeMaxValue l i (i + Power2 j) (Znth (i * K + j) st_ls 0).

Definition STBuiltBeforeLevel
    (l st_ls : list Z) (K n level : Z) : Prop :=
  forall i j,
    0 <= i /\ 0 <= j /\ j < level /\ i + Power2 j <= n ->
    STCellRangeMax l st_ls K i j.

Definition STBuilt (l st_ls : list Z) (K n : Z) : Prop :=
  STBuiltBeforeLevel l st_ls K n K.
