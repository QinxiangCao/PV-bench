Require Export PVbench.Algorithms.discretize.rocq.spec_lib.
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

Definition permutation : list Z -> list Z -> Prop := @Permutation Z.

Definition same_outside_range (l l1 : list Z) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 0 = Znth k l 0.

Definition partitioned_at (l : list Z) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => x <= Znth p l 0) (sublist low p l) /\
  Forall (fun x => Znth p l 0 < x) (sublist (p + 1) (high + 1) l).

Definition partition_scan_inv
    (l l1 : list Z) (low high pivot i j : Z) : Prop :=
  permutation l l1 /\
  same_outside_range l l1 low high /\
  Znth high l1 0 = pivot /\
  Forall (fun x => x <= pivot) (sublist low (i + 1) l1) /\
  Forall (fun x => pivot < x) (sublist (i + 1) j l1).

(* Sorting is an order relation on the selected positions, independent of
   the recursive calls used to establish it. *)
Definition sorted_range (l : list Z) (left right : Z) : Prop :=
  forall i j, 0 <= i -> left <= i -> i <= j -> j <= right ->
    j < Zlength l -> Znth i l 0 <= Znth j l 0.

Definition same_values_prefix
    (out : list Z) (out_len : Z) (src : list Z) (src_len : Z) : Prop :=
  forall x,
    In x (sublist 0 out_len out) <-> In x (sublist 0 src_len src).

Definition dedup_scan_inv
    (src sorted cur : list Z) (slow fast : Z) : Prop :=
  permutation src sorted /\
  increasing sorted /\
  strict_increasing_prefix cur (slow + 1) /\
  same_values_prefix cur (slow + 1) sorted fast /\
  (forall k, fast <= k < Zlength sorted -> Znth k cur 0 = Znth k sorted 0) /\
  Znth slow cur 0 = Znth (fast - 1) sorted 0.

Definition query_forward_search_inv
    (map : list Z) (map_size target low high : Z) : Prop :=
  Forall (fun x => x < target) (sublist 0 low map) /\
  Forall (fun x => target < x) (sublist (high + 1) map_size map).
