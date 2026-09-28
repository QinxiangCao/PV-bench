Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition strict_increasing_prefix (l : list Z) (len : Z) : Prop :=
  forall i j,
    0 <= i < j ->
    j < len ->
    Znth i l 0 < Znth j l 0.

Definition strict_increasing (l : list Z) : Prop :=
  strict_increasing_prefix l (Zlength l).

(* ret is the size of the sorted, duplicate-free output prefix.  Its
   bounds describe the output format, not an input or machine limit. *)
Definition discretize_result (src out : list Z) (ret : Z) : Prop :=
  0 <= ret <= Zlength out /\
  strict_increasing_prefix out ret /\
  (forall x, In x (sublist 0 ret out) <-> In x src).

Definition query_forward_result (map : list Z) (target ret : Z) : Prop :=
  (0 <= ret < Zlength map /\ Znth ret map 0 = target) \/
  (ret = -1 /\ ~ In target map).
