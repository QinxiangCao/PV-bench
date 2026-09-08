Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition KnapsackInputsBounded
    (weights values : list Z) (item_count capacity : Z) : Prop :=
  Zlength weights = item_count /\
  Zlength values = item_count /\
  (forall k, 0 <= k < item_count ->
     1 <= Znth k weights 0 <= capacity + 1) /\
  (forall k, 0 <= k < item_count ->
     0 <= Znth k values 0 <= 10000).
Definition KnapsackTableValuesBounded (dp : list Z) : Prop :=
  forall k, 0 <= k < Zlength dp -> 0 <= Znth k dp 0 <= 4000000.
Definition KnapsackTablePrefixShape
    (dp : list Z) (written : Z) : Prop :=
  0 <= written /\ Zlength dp = written.

(* The following annotation-facing states compose, rather than redefine, the
   separate safety/representation and mathematical predicates. *)
Definition KnapsackPlanWeight (weights picks : list Z) (weight : Z) : Prop :=
  weight = sum (map (fun i => Znth i weights 0) picks).
Definition KnapsackPlanValue
    (weights values picks : list Z) (value : Z) : Prop :=
  Zlength weights = Zlength values /\
  value = sum (map (fun i => Znth i values 0) picks).
Definition KnapsackPlan
    (weights values : list Z) (item_count cap value : Z) : Prop :=
  0 <= item_count <= Zlength weights /\
  Zlength weights = Zlength values /\
  0 <= cap /\
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
Definition KnapsackResultState
    (weights values : list Z) (item_count capacity : Z)
    (dp : list Z) (answer : Z) : Prop :=
  KnapsackMaxValue weights values item_count capacity answer /\
  0 <= answer <= 4000000 /\
  KnapsackTablePrefixShape dp ((item_count + 1) * (capacity + 1)) /\
  KnapsackTableValuesBounded dp /\
  KnapsackRowsDone weights values capacity dp (item_count + 1).

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

(* Helper lemmas migrated from zero_one_knapsack__vc_proving_subagent_merged_proof_manual.v. *)
