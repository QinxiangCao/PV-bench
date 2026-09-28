Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
(* Helper imports migrated from multiple_knapsack__vc_proving_round9_merged_proof_manual.v. *)
Require Import Coq.micromega.Lia.
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

Definition PairwiseWeightValue (xs : list (Z * Z)) : Z :=
  sum (map (fun wp => fst wp * snd wp) xs).

Definition PickWeight (weights picks : list Z) : Z :=
  PairwiseWeightValue (combine weights picks).

Definition PickValue (values picks : list Z) : Z :=
  PairwiseWeightValue (combine values picks).

Definition BoundedPickList
    (weights values counts : list Z) (capacity : Z) (picks : list Z) : Prop :=
  Zlength picks = Zlength values /\
  Zlength picks = Zlength counts /\
  Zlength picks = Zlength weights /\
  Forall2 (fun pick cnt => 0 <= pick <= cnt) picks counts /\
  PickWeight weights picks <= capacity.

Definition MultipleKnapsackAnswer
    (weights values counts : list Z) (capacity answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun picks => BoundedPickList weights values counts capacity picks)
    (fun picks => PickValue values picks)
    answer.
