Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

#[local] Instance finite_vertex_pair (n : Z) :
    Finite (fun e : Z*Z =>
      1 <= fst e < n + 1 /\ 1 <= snd e < n + 1) :=
  Finite_prod (fun x : Z => 1 <= x < n + 1)
              (fun y : Z => 1 <= y < n + 1).

Definition EdgePresent (edges : list (Z*Z)) (removed : (Z*Z) -> Prop)
    (u v : Z) : Prop :=
  (In (u,v) edges \/ In (v,u) edges) /\ ~ removed (u,v) /\ ~ removed (v,u).

Definition ConnectedWithout (edges : list (Z*Z)) (removed : (Z*Z) -> Prop)
    (u v : Z) : Prop :=
  clos_refl_trans (EdgePresent edges removed) u v.

(** Canonical orientation of an undirected edge.  This lets the input-tree
    contract state loop freedom and duplicate freedom independently of the
    orientation used in the input list. *)
Definition CanonicalEdge (edge : Z*Z) : Z*Z :=
  (Z.min (fst edge) (snd edge), Z.max (fst edge) (snd edge)).

Definition SimpleUndirectedEdges (edges : list (Z*Z)) : Prop :=
  (forall edge, In edge edges -> fst edge <> snd edge) /\
  NoDup (map CanonicalEdge edges).

(** A discovery prefix is connected by edges that point strictly backward
    in the prefix.  This is the implementation-independent shape shared by
    breadth-first, depth-first, and other rooted discovery orders. *)
Definition ConnectedDiscoveryPrefix
    (edges : list (Z*Z)) (discovered : list Z) : Prop :=
  forall q,
    0 < q < Zlength discovered ->
    exists parent_pos,
      0 <= parent_pos < q /\
      (In (Znth q discovered 0 + 1,
           Znth parent_pos discovered 0 + 1) edges \/
       In (Znth parent_pos discovered 0 + 1,
           Znth q discovered 0 + 1) edges).

(** Global cut consequence of an undirected tree.  Once a fresh vertex is
    attached to a connected discovered prefix through [parent], none of its
    other neighbors lies in the prefix extended by that vertex.  Unlike a
    cursor-local freshness condition, this property relates adjacency lists
    of every vertex and is stable for any valid rooted discovery order. *)
Definition TreeAttachmentCut (edges : list (Z*Z)) : Prop :=
  forall discovered fresh parent neighbor,
    NoDup discovered ->
    ConnectedDiscoveryPrefix edges discovered ->
    ~ In fresh discovered ->
    In parent discovered ->
    (In (fresh + 1, parent + 1) edges \/
     In (parent + 1, fresh + 1) edges) ->
    (In (fresh + 1, neighbor + 1) edges \/
     In (neighbor + 1, fresh + 1) edges) ->
    neighbor <> parent ->
    ~ In neighbor (discovered ++ (fresh :: nil)).

(** Local projection consumed by one adjacency-build iteration.  It is
    implication-shaped so it remains meaningful at the loop's terminal
    cursor, where there is no current edge. *)
Definition CurrentEdgeFresh (edges : list (Z*Z)) (index : Z) : Prop :=
  0 <= index < Zlength edges ->
  let edge := Znth index edges (0, 0) in
  fst edge <> snd edge /\
  ~ In (CanonicalEdge edge)
      (map CanonicalEdge (sublist 0 index edges)).

Definition ValidRemoval (n k : Z) (edges : list (Z*Z))
    (removed : (Z*Z) -> Prop) : Prop :=
  (forall e, removed e -> In e edges) /\
  #(fun e : Z*Z =>
      (1 <= fst e < n + 1 /\ 1 <= snd e < n + 1) /\ removed e) = k.

Definition CutHasMinimumComponent (n x : Z) (edges : list (Z*Z))
    (removed : (Z*Z) -> Prop) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z * Z =>
      1 <= fst candidate <= n /\
      snd candidate = #(fun u : Z =>
        1 <= u < n + 1 /\ ConnectedWithout edges removed (fst candidate) u))
    snd x.

Definition Spec (n k : Z) (edges : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : ((Z*Z) -> Prop) * Z =>
      ValidRemoval n k edges (fst candidate) /\
      CutHasMinimumComponent n (snd candidate) edges (fst candidate))
    snd out.

(** A threshold is feasible exactly when it does not exceed the optimum.
    This is the implementation-independent decision predicate exposed by
    [feasible] to the binary search. *)
Definition ThresholdFeasible
    (n k : Z) (edges : list (Z*Z)) (minimum : Z) : Prop :=
  exists optimum,
    Spec n k edges optimum /\ minimum <= optimum.

(** Completed rooted traversal: [order_data] is a permutation of all
    zero-based vertices and every non-root vertex names an earlier adjacent
    parent.  This characterizes the mathematical tree order without fixing a
    particular DFS/BFS implementation. *)
Definition RootedOrderModel
    (n : Z) (edges : list (Z*Z))
    (parent_data order_data : list Z) : Prop :=
  1 <= n /\
  Zlength parent_data = n /\
  Zlength order_data = n /\
  Permutation order_data (map Z.of_nat (seq 0 (Z.to_nat n))) /\
  Znth 0 order_data 0 = 0 /\
  Znth 0 parent_data (-1) = -1 /\
  forall q,
    1 <= q < n ->
    exists parent_pos,
      0 <= parent_pos < q /\
      Znth (Znth q order_data 0) parent_data (-1) =
        Znth parent_pos order_data 0 /\
      (In (Znth q order_data 0 + 1,
           Znth parent_pos order_data 0 + 1) edges \/
       In (Znth parent_pos order_data 0 + 1,
           Znth q order_data 0 + 1) edges).

(** Bounds needed at one reverse-scan program point.  The addition bound is
    deliberately about the current cursor only: after one child has been
    accumulated into a parent it need not hold simultaneously for an
    unprocessed sibling. *)
Definition CutScanNodeBounds
    (n cursor : Z) (parent_data order_data sizes : list Z) : Prop :=
  Zlength sizes = n /\
  (forall vertex, 0 <= vertex < n ->
    0 <= Znth vertex sizes 0 <= n) /\
  (0 <= cursor ->
    let vertex := Znth cursor order_data 0 in
    Znth vertex parent_data (-1) >= 0 ->
    Znth (Znth vertex parent_data (-1)) sizes 0 +
      Znth vertex sizes 0 <= n).

(** One mathematical reverse-scan update.  It records the two semantic
    choices made for the current rooted-tree vertex: whether its completed
    subtree forms a component, and whether the residual size is propagated
    to a parent. *)
Definition CutScanStep
    (n minimum cursor components : Z)
    (parent_data order_data sizes : list Z)
    (next_components : Z) (next_sizes : list Z) : Prop :=
  let vertex := Znth cursor order_data 0 in
  exists cut_sizes,
    ((Znth vertex sizes 0 >= minimum /\
      next_components = components + 1 /\
      cut_sizes = replace_Znth vertex 0 sizes) \/
     (Znth vertex sizes 0 < minimum /\
      next_components = components /\
      cut_sizes = sizes)) /\
    ((Znth vertex parent_data (-1) >= 0 /\
      next_sizes =
        replace_Znth (Znth vertex parent_data (-1))
          (Znth (Znth vertex parent_data (-1)) cut_sizes 0 +
           Znth vertex cut_sizes 0) cut_sizes) \/
     (Znth vertex parent_data (-1) < 0 /\
      next_sizes = cut_sizes)) /\
    CutScanNodeBounds n (cursor - 1)
      parent_data order_data next_sizes.

(** Relational continuation of the remaining reverse scan.  Unlike a
    terminal-only assertion, this relation is inductive at every cursor: a
    loop update exposes exactly the continuation required by the next
    invariant state. *)
Inductive ReverseCutScan
    (n minimum : Z) (parent_data order_data : list Z) :
    Z -> Z -> list Z -> Z -> list Z -> Prop :=
| reverse_cut_scan_done : forall components sizes,
    CutScanNodeBounds n (-1) parent_data order_data sizes ->
    ReverseCutScan n minimum parent_data order_data
      (-1) components sizes components sizes
| reverse_cut_scan_step : forall cursor components sizes
    next_components next_sizes final_components final_sizes,
    0 <= cursor ->
    CutScanNodeBounds n cursor parent_data order_data sizes ->
    CutScanStep n minimum cursor components parent_data order_data sizes
      next_components next_sizes ->
    ReverseCutScan n minimum parent_data order_data
      (cursor - 1) next_components next_sizes
      final_components final_sizes ->
    ReverseCutScan n minimum parent_data order_data
      cursor components sizes final_components final_sizes.

(** Mathematical bridge for the greedy reverse scan on any completed rooted
    order.  It is quantified over the all-ones input list, rather than tied to
    the concrete allocation history used to produce that list. *)
Definition CutScanReady
    (n k : Z) (edges : list (Z*Z))
    (parent_data order_data : list Z) : Prop :=
  forall minimum sizes,
    1 <= minimum <= n ->
    Zlength sizes = n ->
    (forall vertex, 0 <= vertex < n -> Znth vertex sizes 0 = 1) ->
    exists final_components final_sizes,
      ReverseCutScan n minimum parent_data order_data
        (n - 1) 0 sizes final_components final_sizes /\
      0 <= final_components <= n /\
      Zlength final_sizes = n /\
      (forall vertex, 0 <= vertex < n ->
        0 <= Znth vertex final_sizes 0 <= n) /\
      (final_components >= k + 1 <->
       ThresholdFeasible n k edges minimum).

(** The freshly allocated scratch buffer has an exact logical contents list,
    rather than merely an existential list of the right length. *)
Definition FreshSizeCells (n : Z) (cells : list (option Z)) : Prop :=
  cells = repeat None (Z.to_nat n).

(** Valid inputs include the two implementation-independent existence facts
    consumed later: the bounded optimum and correctness of the greedy scan
    for any mathematical rooted order of the input tree. *)
Definition Pre (n k : Z) (edges : list (Z*Z)) : Prop :=
  1 <= k < n /\
  n <= 100000 /\
  Zlength edges = n - 1 /\
  Forall (fun e => 1 <= fst e <= n /\ 1 <= snd e <= n) edges /\
  SimpleUndirectedEdges edges /\
  TreeAttachmentCut edges /\
  (forall index, CurrentEdgeFresh edges index) /\
  (forall v, 1 <= v <= n ->
    ConnectedWithout edges (fun _ => False) 1 v) /\
  (exists optimum,
    Spec n k edges optimum /\ 1 <= optimum <= n / (k + 1)) /\
  forall parent_data order_data,
    RootedOrderModel n edges parent_data order_data ->
    CutScanReady n k edges parent_data order_data.
