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
From AUXLib Require Import MonotonicList int_auto Axioms Feq Idents ListLib VMap.
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


Require Export PVbench.Algorithms.sort_point.rocq.spec_lib.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition PolarLt (gp a b : point) : Prop :=
  PolarCmpResult gp a b (-1).

Definition PointSortedRange (gp : point) (l : list point) (left right : Z) : Prop :=
  forall i j,
    left <= i ->
    i <= j ->
    j <= right ->
    PolarLe gp (Znth i l default_point) (Znth j l default_point).

Definition PointSameOutsideRange (l l1 : list point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  Forall2 eq
    (map (fun k => Znth k l1 default_point)
      (filter (fun k : Z => orb (Z.ltb k left) (Z.ltb right k)) (Zrange 0 (Zlength l))))
    (map (fun k => Znth k l default_point)
      (filter (fun k : Z => orb (Z.ltb k left) (Z.ltb right k)) (Zrange 0 (Zlength l)))).
Definition PointFlatModel (flat : list Z) : Prop :=
  exists pts, FlatPoints flat pts.

Definition PointRangeSortResult
  (gp : point) (flat_in : list Z) (pts_out : list point)
  (left right : Z) : Prop :=
  forall pts_in,
    FlatPoints flat_in pts_in ->
    PointPermutation pts_in pts_out /\
    PointSameOutsideRange pts_in pts_out left right /\
    PointSortedRange gp pts_out left right.

Definition PointPartitionedAt
  (gp : point) (l : list point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => PolarLe gp x (Znth p l default_point)) (sublist low p l) /\
  Forall (fun x => PolarLt gp (Znth p l default_point) x)
         (sublist (p + 1) (high + 1) l).

Definition PointPartitionScanInv
  (gp : point) (before cur : list point)
  (low high : Z) (pivot : point) (i j : Z) : Prop :=
  PointPermutation before cur /\
  PointSameOutsideRange before cur low high /\
  Znth high cur default_point = pivot /\
  Forall (fun p => PolarLe gp p pivot) (sublist low (i + 1) cur) /\
  Forall (PolarLt gp pivot) (sublist (i + 1) j cur).

Definition point_swap_points (l : list point) (i j : Z) : list point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

Definition point_swap_flat (flat : list Z) (i j : Z) : list Z :=
  let xi := Znth (2 * i) flat 0 in
  let yi := Znth (2 * i + 1) flat 0 in
  let xj := Znth (2 * j) flat 0 in
  let yj := Znth (2 * j + 1) flat 0 in
  replace_Znth (2 * j + 1) yi
    (replace_Znth (2 * j) xi
      (replace_Znth (2 * i + 1) yj
        (replace_Znth (2 * i) xj flat))).

(* Helper imports migrated from sort_point__vc_proving_subagent_tmp_proof_manual__merged_r4.v. *)
Require Import Coq.Strings.Ascii.

(* Helper lemmas migrated from sort_point__vc_proving_subagent_tmp_proof_manual__merged_r4.v. *)
