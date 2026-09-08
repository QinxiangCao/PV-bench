Require Import PVbench.Codeforces.examples_shard00.P049_1946C_tree_cutting.rocq.spec_lib.

#[local] Existing Instance finite_vertex_pair.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(** The linked-list cursor relation induced by [next_data]. *)
Definition AdjacencyNext (next_data : list Z) (from to : Z) : Prop :=
  0 <= from < Zlength next_data /\
  to = Znth from next_data (-1).

Definition AdjacencySlot
    (head_data next_data : list Z) (u slot : Z) : Prop :=
  0 <= u < Zlength head_data /\
  0 <= slot < Zlength next_data /\
  clos_refl_trans (AdjacencyNext next_data)
    (Znth u head_data (-1)) slot.

(** Prefix representation while the adjacency arrays are being built. *)
Definition AdjacencyBuildState
    (n : Z) (edges : list (Z*Z)) (done : Z)
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

(** Exact mathematical interpretation of the three flat adjacency arrays.
    Vertices in [edges] are one-based; array vertices are zero-based. *)
Definition AdjacencyModel
    (n : Z) (edges : list (Z*Z))
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

(** Prefix state of the iterative rooted traversal.  [order_data] is exactly
    the discovered sequence, while [parent_cells] records which scattered
    parent-array cells have been initialized. *)
Definition TraversalState
    (n : Z) (edges : list (Z*Z)) (processed : Z)
    (order_data : list Z) (parent_cells : list (option Z)) : Prop :=
  Zlength parent_cells = n /\
  0 <= processed <= Zlength order_data /\
  1 <= Zlength order_data <= n /\
  NoDup order_data /\
  Znth 0 order_data 0 = 0 /\
  (forall q,
    0 <= q < Zlength order_data ->
    let vertex := Znth q order_data 0 in
    0 <= vertex < n /\
    exists parent_vertex,
      Znth vertex parent_cells None = Some parent_vertex /\
      ((q = 0 /\ parent_vertex = -1) \/
       exists parent_pos,
         0 <= parent_pos < q /\
         parent_vertex = Znth parent_pos order_data 0 /\
         (In (vertex + 1, parent_vertex + 1) edges \/
          In (parent_vertex + 1, vertex + 1) edges))) /\
  (forall q neighbor,
    0 <= q < processed ->
    (In (Znth q order_data 0 + 1, neighbor + 1) edges \/
     In (neighbor + 1, Znth q order_data 0 + 1) edges) ->
    In neighbor order_data) /\
  forall q neighbor parent_vertex,
    processed < q < Zlength order_data ->
    Znth (Znth q order_data 0) parent_cells None = Some parent_vertex ->
    (In (Znth q order_data 0 + 1, neighbor + 1) edges \/
     In (neighbor + 1, Znth q order_data 0 + 1) edges) ->
    neighbor <> parent_vertex ->
    ~ In neighbor order_data.

(** State at the boundary before scanning the current vertex.  The pending
    clause in [TraversalState] deliberately starts strictly after
    [processed], because children discovered while scanning the current
    vertex are appended to [order_data].  At entry, however, every
    non-parent neighbor of that current vertex is still undiscovered. *)
Definition TraversalEntryState
    (n : Z) (edges : list (Z*Z)) (processed : Z)
    (order_data : list Z) (parent_cells : list (option Z)) : Prop :=
  TraversalState n edges processed order_data parent_cells /\
  (processed < Zlength order_data ->
   let vertex := Znth processed order_data 0 in
   exists parent_vertex,
     Znth vertex parent_cells None = Some parent_vertex /\
     forall neighbor,
       (In (vertex + 1, neighbor + 1) edges \/
        In (neighbor + 1, vertex + 1) edges) ->
       neighbor <> parent_vertex ->
       ~ In neighbor order_data).

Definition TraversalAdjState
    (n : Z) (edges : list (Z*Z))
    (processed : Z) (order_data : list Z)
    (parent_cells : list (option Z))
    (head_data to_data next_data : list Z)
    (vertex parent_vertex cursor : Z) : Prop :=
  TraversalState n edges processed order_data parent_cells /\
  (-1 <= cursor < 2 * n - 2) /\
  0 <= vertex < n /\
  Znth vertex parent_cells None = Some parent_vertex /\
  (cursor = -1 \/
   AdjacencySlot head_data next_data vertex cursor) /\
  (forall slot,
    AdjacencySlot head_data next_data vertex slot ->
    (cursor = -1 \/
     ~ clos_refl_trans (AdjacencyNext next_data) cursor slot) ->
    In (Znth slot to_data 0) order_data) /\
  (forall slot,
    AdjacencySlot head_data next_data vertex slot ->
    clos_refl_trans (AdjacencyNext next_data) cursor slot ->
    Znth slot to_data 0 <> parent_vertex ->
    ~ In (Znth slot to_data 0) order_data) /\
  (cursor <> -1 ->
    0 <= Znth cursor to_data 0 < n) /\
  (cursor <> -1 -> Znth cursor to_data 0 <> parent_vertex ->
    ~ In (Znth cursor to_data 0) order_data /\
    Zlength order_data < n) /\
  (cursor = -1 ->
    forall neighbor,
      (In (vertex + 1, neighbor + 1) edges \/
       In (neighbor + 1, vertex + 1) edges) ->
      In neighbor order_data).

(** Exact written prefix of the overwrite-to-one loop.  The matching C
    invariant owns this list as a concrete segment and owns the unprocessed
    suffix with [undef_seg], so every feasibility call may safely overwrite
    the whole scratch buffer regardless of its previous values. *)
Definition SizeInitializationState
    (n cursor : Z) (initialized : list Z) : Prop :=
  0 <= cursor <= n /\
  Zlength initialized = cursor /\
  forall j, 0 <= j < cursor -> Znth j initialized 0 = 1.

(** Reverse traversal state.  Every cursor owns a continuation to the same
    final component count, so both loop branches preserve the threshold
    decision without manufacturing a new fact at cursor zero. *)
Definition CutScanState
    (n k : Z) (edges : list (Z*Z))
    (minimum cursor components : Z)
    (parent_data order_data sizes : list Z) : Prop :=
  -1 <= cursor < n /\
  0 <= components <= n - 1 - cursor /\
  Zlength parent_data = n /\
  Zlength order_data = n /\
  RootedOrderModel n edges parent_data order_data /\
  CutScanNodeBounds n cursor parent_data order_data sizes /\
  exists final_components final_sizes,
    ReverseCutScan n minimum parent_data order_data
      cursor components sizes final_components final_sizes /\
    0 <= final_components <= n /\
    Zlength final_sizes = n /\
    (forall vertex, 0 <= vertex < n ->
      0 <= Znth vertex final_sizes 0 <= n) /\
    (final_components >= k + 1 <->
     ThresholdFeasible n k edges minimum).

(** Binary-search invariant stated against the mathematical optimum rather
    than against an executable mirror of the search loop. *)
Definition SearchState
    (n k : Z) (edges : list (Z*Z))
    (lo hi best : Z) : Prop :=
  1 <= lo <= n + 1 /\
  0 <= hi <= n /\
  1 <= best <= n /\
  exists optimum,
    Spec n k edges optimum /\
    1 <= optimum <= n /\
    1 <= best <= optimum /\
    ((lo <= optimum <= hi) \/
     (best = optimum /\ optimum < lo)).
