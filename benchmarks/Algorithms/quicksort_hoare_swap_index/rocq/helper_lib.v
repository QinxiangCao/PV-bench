Require Export PVbench.Algorithms.quicksort_hoare_swap_index.rocq.spec_lib.
Require Import SumLib.ZRange.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib MonotonicList VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition same_outside_range (l l1 : list Z) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  Forall2 eq
    (map (fun k => Znth k l1 0)
      (filter (fun k : Z => orb (Z.ltb k left) (Z.ltb right k)) (Zrange 0 (Zlength l))))
    (map (fun k => Znth k l 0)
      (filter (fun k : Z => orb (Z.ltb k left) (Z.ltb right k)) (Zrange 0 (Zlength l)))).

Definition partitioned_at (l : list Z) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => x <= Znth p l 0) (sublist low p l) /\
  Forall (fun x => Znth p l 0 <= x) (sublist (p + 1) (high + 1) l).

Definition range_nondecreasing (l : list Z) (left right : Z) : Prop :=
  forall i j,
    left <= i ->
    i <= j ->
    j <= right ->
    Znth i l 0 <= Znth j l 0.
