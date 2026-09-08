Require Import PVbench.Algorithms.discretize.rocq.spec_lib.

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

Definition permutation : list Z -> list Z -> Prop := @Permutation Z.
Fixpoint increasing_aux (l : list Z) (x : Z) : Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ increasing_aux l0 y
  end.
Definition increasing (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: l0 => increasing_aux l0 x
  end.
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
  (forall k, low <= k <= i -> Znth k l1 0 <= pivot) /\
  (forall k, i < k < j -> pivot < Znth k l1 0).
Inductive sorted_range (l : list Z) (left right : Z) : Prop :=
| sorted_range_base :
    left >= right ->
    sorted_range l left right
| sorted_range_from_left : forall p,
    p >= right ->
    partitioned_at l left right p ->
    sorted_range l left (p - 1) ->
    sorted_range l left right
| sorted_range_from_right : forall p,
    p <= left ->
    partitioned_at l left right p ->
    sorted_range l (p + 1) right ->
    sorted_range l left right
| sorted_range_from_both : forall p,
    left <= p <= right ->
    partitioned_at l left right p ->
    sorted_range l left (p - 1) ->
    sorted_range l (p + 1) right ->
    sorted_range l left right.
Definition strict_increasing (l : list Z) : Prop :=
  strict_increasing_prefix l (Zlength l).
Definition dedup_scan_inv
    (src sorted cur : list Z) (slow fast : Z) : Prop :=
  Zlength src = Zlength sorted /\
  Zlength cur = Zlength sorted /\
  permutation src sorted /\
  increasing sorted /\
  1 <= fast <= Zlength sorted /\
  0 <= slow < fast /\
  strict_increasing_prefix cur (slow + 1) /\
  same_values_prefix cur (slow + 1) sorted fast /\
  (forall k, fast <= k < Zlength sorted -> Znth k cur 0 = Znth k sorted 0) /\
  Znth slow cur 0 = Znth (fast - 1) sorted 0.
Definition query_forward_result
    (map : list Z) (map_size target ret : Z) : Prop :=
  ((exists i,
      0 <= i < map_size /\
      Znth i map 0 = target /\
      ret = i) /\
   (forall j,
      0 <= j < map_size ->
      Znth j map 0 = target ->
      ret = j)) \/
  ((forall i, 0 <= i < map_size -> Znth i map 0 <> target) /\
   ret = -1).
Definition query_forward_search_inv
    (map : list Z) (map_size target low high : Z) : Prop :=
  0 <= low /\
  high < map_size /\
  low <= high + 1 /\
  (forall i, 0 <= i < low -> Znth i map 0 < target) /\
  (forall i, high < i < map_size -> target < Znth i map 0).
