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

(* Mathematical selections, optimum and completed table entries.
   Input bounds, storage shape and machine limits belong to C annotations. *)
Definition KnapsackPlanWeight (weights picks : list Z) (weight : Z) : Prop :=
  weight = sum (map (fun i => Znth i weights 0) picks).

Definition KnapsackPlanValue
    (weights values picks : list Z) (value : Z) : Prop :=
  value = sum (map (fun i => Znth i values 0) picks).

Definition KnapsackPlan
    (weights values : list Z) (item_count cap value : Z) : Prop :=
  exists picks weight,
    NoDup picks /\
    Forall (fun i => 0 <= i < item_count) picks /\
    KnapsackPlanWeight weights picks weight /\
    weight <= cap /\
    KnapsackPlanValue weights values picks value.

Definition KnapsackMaxValue
    (weights values : list Z) (item_count cap answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun value => KnapsackPlan weights values item_count cap value)
    (fun value => value)
    answer.
