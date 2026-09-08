Require Import PVbench.Codeforces.examples_shard00.P057_1067B_multihedgehog.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import GraphLib.graph_basic.

Require Import GraphLib.reachable.vpath.

Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.

Import ListNotations.

Local Open Scope Z_scope.

Definition AdjacencyNext (next_data : list Z) (from to : Z) : Prop :=
  0 <= from < Zlength next_data /\
  to = Znth from next_data (-1).

Definition AdjacencySlot
    (head_data next_data : list Z) (u slot : Z) : Prop :=
  0 <= u < Zlength head_data /\
  0 <= slot < Zlength next_data /\
  clos_refl_trans (AdjacencyNext next_data)
    (Znth u head_data (-1)) slot.

Definition AdjacencyBuildState
    (n : Z) (edges : list (Z * Z)) (done : Z)
    (head_data to_data next_data : list Z) : Prop :=
  0 <= done <= Zlength edges /\
  Zlength head_data = n /\
  Zlength to_data = 2 * done /\
  Zlength next_data = 2 * done /\
  (forall u, 0 <= u < n ->
    Znth u head_data (-1) = -1 \/
    0 <= Znth u head_data (-1) < 2 * done) /\
  (forall slot, 0 <= slot < 2 * done ->
    0 <= Znth slot to_data 0 < n /\
    (Znth slot next_data (-1) = -1 \/
     0 <= Znth slot next_data (-1) < slot)) /\
  (forall u v,
    0 <= u < n -> 0 <= v < n ->
    (In (u + 1, v + 1) (sublist 0 done edges) \/
     In (v + 1, u + 1) (sublist 0 done edges) <->
     exists slot,
       AdjacencySlot head_data next_data u slot /\
       Znth slot to_data 0 = v)) /\
  forall u slot1 slot2,
    AdjacencySlot head_data next_data u slot1 ->
    AdjacencySlot head_data next_data u slot2 ->
    Znth slot1 to_data 0 = Znth slot2 to_data 0 ->
    slot1 = slot2.

Definition AdjacencyModel
    (n : Z) (edges : list (Z * Z))
    (head_data to_data next_data : list Z) : Prop :=
  Zlength head_data = n /\
  Zlength to_data = 2 * n - 2 /\
  Zlength next_data = 2 * n - 2 /\
  Zlength edges = n - 1 /\
  (forall u, 0 <= u < n ->
    Znth u head_data (-1) = -1 \/
    0 <= Znth u head_data (-1) < 2 * n - 2) /\
  (forall slot, 0 <= slot < 2 * n - 2 ->
    0 <= Znth slot to_data 0 < n /\
    (Znth slot next_data (-1) = -1 \/
     0 <= Znth slot next_data (-1) < slot)) /\
  (forall u v,
    0 <= u < n -> 0 <= v < n ->
    (In (u + 1, v + 1) edges \/ In (v + 1, u + 1) edges <->
     exists slot,
       AdjacencySlot head_data next_data u slot /\
       Znth slot to_data 0 = v)) /\
  forall u slot1 slot2,
    AdjacencySlot head_data next_data u slot1 ->
    AdjacencySlot head_data next_data u slot2 ->
    Znth slot1 to_data 0 = Znth slot2 to_data 0 ->
    slot1 = slot2.

Definition AdjacencyScanState
    (head_data to_data next_data : list Z) (vertex cursor : Z)
    (queue : list Z) : Prop :=
  forall slot,
    AdjacencySlot head_data next_data vertex slot ->
    clos_refl_trans (AdjacencyNext next_data) cursor slot \/
    In (Znth slot to_data 0) queue.

Definition BFSAdjState
    (n : Z) (edges : list (Z * Z)) (source processed farthest : Z)
    (queue parents distances head_data to_data next_data : list Z)
    (vertex cursor : Z) : Prop :=
  BFSQueueState n edges source (processed - 1) farthest queue parents distances /\
  0 < processed <= Zlength queue /\
  vertex = Znth (processed - 1) queue 0 /\
  Znth vertex distances (-1) <= Znth farthest distances (-1) /\
  (-1 <= cursor < 2 * n - 2) /\
  (cursor = -1 \/ AdjacencySlot head_data next_data vertex cursor) /\
  (cursor <> -1 -> 0 <= Znth cursor to_data 0 < n) /\
  BFSFrontierState n edges source vertex distances /\
  AdjacencyScanState head_data to_data next_data vertex cursor queue /\
  (cursor = -1 ->
    forall neighbor,
      (In (vertex + 1, neighbor + 1) edges \/
       In (neighbor + 1, vertex + 1) edges) ->
      In neighbor queue).

Definition DiameterDecision
    (k : Z) (second_dist : list Z) (endpoint out : Z) : Prop :=
  (out = 0 /\ Znth endpoint second_dist 0 <> 2 * k) \/
  (out = 1 /\ Znth endpoint second_dist 0 = 2 * k).

Definition SolverCertificate
    (n k : Z) (edges : list (Z * Z))
    (first_parent first_dist : list Z) (first_endpoint : Z)
    (second_parent second_dist : list Z) (second_endpoint center : Z)
    (center_parent center_dist degrees : list Z) (out : Z) : Prop :=
  BFSResult n edges 0 first_parent first_dist first_endpoint /\
  BFSResult n edges first_endpoint second_parent second_dist second_endpoint /\
  DegreePrefix n edges (n - 1) degrees /\
  SolverDecision n k edges second_parent second_dist second_endpoint center
    center_parent center_dist degrees n out.
