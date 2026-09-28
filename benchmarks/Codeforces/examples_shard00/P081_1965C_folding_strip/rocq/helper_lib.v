Require Export PVbench.Codeforces.examples_shard00.P081_1965C_folding_strip.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition SpecEdges (s : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ValidFoldedPlacementEdges s (fst candidate) (snd candidate))
    snd out.

Definition AlternatingWalkExtrema
    (s boundaries : list Z) (cur mn mx : Z) : Prop :=
  Zlength boundaries = Zlength s + 1 /\
  Znth 0 boundaries 0 = 0 /\
  Znth (Zlength s) boundaries 0 = cur /\
  (forall k, 0 <= k < Zlength s ->
    Z.abs (Znth (k + 1) boundaries 0 - Znth k boundaries 0) = 1) /\
  (forall k, 0 <= k < Zlength s ->
    (Znth k s 0 = 49 <->
     Z.even (edge_lower boundaries k) = true)) /\
  (forall k, 0 <= k < Zlength boundaries ->
    mn <= Znth k boundaries 0 <= mx) /\
  In mn boundaries /\ In mx boundaries.

Definition FoldPrefixState
    (s : list Z) (i cur mn mx : Z) : Prop :=
  0 <= i <= Zlength s /\
  exists boundaries,
    AlternatingWalkExtrema (sublist 0 i s) boundaries cur mn mx /\
    (forall candidate width,
      ValidFoldedPlacementEdges (sublist 0 i s) candidate width ->
      mx - mn <= width).

Definition FoldPrefixAlternatingState
    (s : list Z) (i cur mn mx : Z) : Prop :=
  0 <= i <= Zlength s /\
  exists boundaries,
    AlternatingWalkExtrema (sublist 0 i s) boundaries cur mn mx /\
    (forall candidate width,
      AlternatingLabelPlacement (sublist 0 i s) candidate width ->
      mx - mn <= width).

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.
