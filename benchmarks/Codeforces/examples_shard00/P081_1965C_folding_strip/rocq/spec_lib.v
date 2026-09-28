Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ValidFoldedPlacement (s positions : list Z) (width : Z) : Prop :=
  Zlength positions = Zlength s /\ 1 <= width <= Zlength s /\
  Forall (fun p => 0 <= p < width) positions /\
  (forall i, 0 <= i < Zlength positions - 1 ->
    Z.abs (Znth (i+1) positions 0 - Znth i positions 0) = 1) /\
  (forall i j, 0 <= i < Zlength s -> 0 <= j < Zlength s ->
    Znth i positions 0 = Znth j positions 0 -> Znth i s 0 = Znth j s 0) /\
  (forall p, 0 <= p < width -> In p positions).

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\ Forall (fun c => c = 48 \/ c = 49) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ValidFoldedPlacement s (fst candidate) (snd candidate))
    snd out.

Definition edge_lower (boundaries : list Z) (i : Z) : Z :=
  Z.min (Znth i boundaries 0) (Znth (i + 1) boundaries 0).

Definition ValidFoldedPlacementEdges
    (s boundaries : list Z) (width : Z) : Prop :=
  Zlength boundaries = Zlength s + 1 /\
  1 <= width <= Zlength s /\
  Forall (fun p => 0 <= p <= width) boundaries /\
  (forall i, 0 <= i < Zlength s ->
    Z.abs (Znth (i + 1) boundaries 0 - Znth i boundaries 0) = 1) /\
  (forall i j, 0 <= i < Zlength s -> 0 <= j < Zlength s ->
    edge_lower boundaries i = edge_lower boundaries j ->
    Znth i s 0 = Znth j s 0) /\
  (forall p, 0 <= p < width ->
    exists i, 0 <= i < Zlength s /\ edge_lower boundaries i = p).

Definition AlternatingLabelPlacement
    (s boundaries : list Z) (width : Z) : Prop :=
  ValidFoldedPlacementEdges s boundaries width /\
  exists phase : bool,
    forall i, 0 <= i < Zlength s ->
      (Znth i s 0 = 49 <->
       Z.even (edge_lower boundaries i) = phase).

Definition SpecAlternatingEdges (s : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      AlternatingLabelPlacement s (fst candidate) (snd candidate))
    snd out.

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.
