Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass.
From GraphLib Require Import Zweight.
From GraphLib Require Import dijkstra.
From GraphLib Require Import epath.
From MaxMinLib Require Import Interface.
Require Import Algorithms.Dijkstra.Dijkstra.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelBasic StateRelMonad.
Require Import Logic.LogicGenerator.demo932.Interface.
(* ---- merged from the former common_helper_lib.v ---- *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From AUXLib Require Import ListLib.
From MonadLib Require Import MonadLib.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelMonad.
From MaxMinLib Require Import MaxMin Interface.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight dijkstra.
Require Import Algorithms.Dijkstra.Dijkstra.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export PVbench.Algorithms.Dijkstra_linked_forward_star_index_queue.rocq.spec_lib.

Import ListNotations.
Import SetsNotation.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope monad.
Import naive_C_Rules.
Local Open Scope sac.

Module DijkstraLinkedForwardStar.

Definition state : Type := @St Z.

#[local] Existing Instance DijkstraGraph.weight_instance.

Notation dijkstra_step_aux := (@step_aux DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance).
Notation dijkstra_weight := (@weight DijkstraGraph.G DijkstraGraph.E DijkstraGraph.weight_instance).
Notation dijkstra_valid_epath := (@valid_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_epath_weight := (@epath_weight DijkstraGraph.G DijkstraGraph.E DijkstraGraph.weight_instance).
Notation dijkstra_is_epath_through_vset := (@is_epath_through_vset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_reachable := (@reachable DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance).
Notation dijkstra_min_epath := (@min_value_weight_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance).
Notation dijkstra_min_epath_in_vset := (@min_value_weight_epath_in_vset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance).

Definition shortest_path_relaxation_bounded
    (g : DijkstraGraph.G) (src bound : Z) : Prop :=
  @GraphLib.reachable.epath.shortest_path_relaxation_bounded
    DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
    DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
    DijkstraGraph.PathData DijkstraGraph.path_instance
    DijkstraGraph.weight_instance
    g src bound.

Notation dijkstra_visited_dist_final := (fun g src s => @visited_dist_final DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance src s).
Notation dijkstra_unvisited_dist_optimal := (fun g src s => @unvisited_dist_optimal DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance src s).

Notation dijkstra_visited_le_unvisited := (@visited_le_unvisited Z).

Notation dijkstra_first_step_invariant := (fun g src done s => @Dijkstra.first_step_invariant DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance g DijkstraGraph.weight_instance src done s).
Notation dijkstra_relax_step_invariant := (fun g cur_vertex s0 done s => @Dijkstra.relax_step_invariant DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance g DijkstraGraph.weight_instance cur_vertex s0 done s).

Definition initial_state (src : Z) : state :=
  @initSt Z DijkstraGraph.vertex_eqdec src.

Notation dijkstra_distance_correct := (fun g src s => @distance_correct DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance src s).
Notation dijkstra_valid_epath_cons_inv := (@valid_epath_cons_inv DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance).
Notation dijkstra_valid_epath_nil_inv := (@valid_epath_nil_inv DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_valid_epath_inv_n1 := (@valid_epath_inv_n1 DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance).
Notation dijkstra_reachable_valid_epath := (@reachable_valid_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance).
Notation dijkstra_valid_epath_reachable := (@valid_epath_reachable DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance).
Notation dijkstra_is_epath_through_vset_single := (@is_epath_through_vset_single DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.single_path_instance).
Notation dijkstra_is_epath_through_vset_subset := (@is_epath_through_vset_subset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).

Notation dijkstra_is_epath_through_vset_greedy_cut := (fun g Hwf u p v S Hpath Hunvisited => @is_epath_through_vset_greedy_cut DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance DijkstraGraph.stepunique_instance g Hwf u p v S Hpath Hunvisited).
Notation dijkstra_greedy_choice_correct := (fun g Hwf src Hnonneg u S dist => @dijkstra.dijkstra_greedy_choice_correct DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.stepunique_instance g Hwf DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance DijkstraGraph.weight_instance src Hnonneg u S dist).
Notation dijkstra_visited_keep := (fun g src u v S e dist => @dijkstra.dijkstra_visited_keep DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.weight_instance src u v S e dist).
Notation dijkstra_invariant_implies_final := (fun g Hwf src Hnonneg cur_vertex s0 s1 => @Dijkstra.invariant_implies_final DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.stepunique_instance DijkstraGraph.simple_graph_instance g Hwf DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance DijkstraGraph.weight_instance src Hnonneg cur_vertex s0 s1).

Definition storage_index (i : Z) : Prop :=
  0 <= i < DijkstraGraph.max_vertices.

Definition max_priority_queue_size : Z := 200005.

Definition edge_index (edge_count i : Z) : Prop :=
  0 <= i < edge_count.

Definition dist_cell (values : list Z) (v : Z) : Z :=
  Znth v values DijkstraGraph.infinity.

Definition distance_as_cell (d : option Z) : Z :=
  DijkstraGraph.distance_as_cell d.

Definition cell_as_distance (x : Z) : option Z :=
  DijkstraGraph.cell_as_distance x.

Definition vector_shape (values : list Z) : Prop :=
  Zlength values = DijkstraGraph.max_vertices.

Definition dist_values_safe (values : list Z) : Prop :=
  forall v, storage_index v ->
    0 <= dist_cell values v <= DijkstraGraph.infinity.

Definition dist_init_loop (i : Z) (values : list Z) : Prop :=
  vector_shape values /\
  0 <= i <= DijkstraGraph.max_vertices /\
  forall v,
    storage_index v ->
    v < i ->
    dist_cell values v = DijkstraGraph.infinity.

Definition graph_has_size (g : DijkstraGraph.G) (n : Z) : Prop :=
  DijkstraGraph.vertex_count g = n /\
  0 <= n <= DijkstraGraph.max_vertices.

Definition vertex_valid (g : DijkstraGraph.G) (v : Z) : Prop :=
  DijkstraGraph.vertex_valid g v.

Inductive next_chain (next_values : list Z) : Z -> Z -> Prop :=
| next_chain_here : forall e,
    0 <= e < Zlength next_values ->
    next_chain next_values e e
| next_chain_next : forall cur e,
    0 <= cur < Zlength next_values ->
    Znth cur next_values (-1) <> -1 ->
    next_chain next_values (Znth cur next_values (-1)) e ->
    next_chain next_values cur e.

Definition forward_star_edge
  (head_values to_values weight_values next_values : list Z)
  (u v w : Z) : Prop :=
  storage_index u /\
  exists e,
    next_chain next_values (Znth u head_values (-1)) e /\
    0 <= e < Zlength to_values /\
    Znth e to_values 0 = v /\
    Znth e weight_values 0 = w.

Definition edge_values_safe
    (vertex_count edge_count : Z)
    (to_values weight_values next_values : list Z) : Prop :=
  Zlength to_values = edge_count /\
  Zlength weight_values = edge_count /\
  Zlength next_values = edge_count /\
  forall e,
    edge_index edge_count e ->
    0 <= Znth e to_values 0 < vertex_count /\
    storage_index (Znth e to_values 0) /\
    0 <= Znth e weight_values 0 <= DijkstraGraph.infinity /\
    (Znth e next_values (-1) = -1 \/
      edge_index edge_count (Znth e next_values (-1))).

Definition head_values_safe
    (vertex_count edge_count : Z) (head_values : list Z) : Prop :=
  Zlength head_values = vertex_count /\
  forall u,
    0 <= u < vertex_count ->
    Znth u head_values (-1) = -1 \/
    edge_index edge_count (Znth u head_values (-1)).

Definition forward_star_chain_wf
    (head_values to_values next_values : list Z) : Prop :=
  (forall edge,
    0 <= edge < Zlength next_values ->
    Znth edge next_values (-1) <> -1 ->
    ~ next_chain next_values (Znth edge next_values (-1)) edge) /\
  (forall u i j,
    storage_index u ->
    next_chain next_values (Znth u head_values (-1)) i ->
    next_chain next_values (Znth u head_values (-1)) j ->
    0 <= i < Zlength to_values ->
    0 <= j < Zlength to_values ->
    Znth i to_values 0 = Znth j to_values 0 ->
    i = j) /\
  forall u edge,
    storage_index u ->
    Znth u head_values (-1) <> -1 ->
    next_chain next_values (Znth u head_values (-1)) edge ->
    0 <= edge < Zlength next_values.

Definition forward_star_model
    (g : DijkstraGraph.G) (edge_count : Z)
    (head_values to_values weight_values next_values : list Z) : Prop :=
  DijkstraGraph.graph_wf g /\
  graph_has_size g (Zlength head_values) /\
  0 <= edge_count <= max_priority_queue_size /\
  head_values_safe (DijkstraGraph.vertex_count g) edge_count head_values /\
  edge_values_safe
    (DijkstraGraph.vertex_count g) edge_count
    to_values weight_values next_values /\
  (forall u v w,
    vertex_valid g u ->
    vertex_valid g v ->
    (DijkstraGraph.edge_weight g u v = Some w <->
      forward_star_edge head_values to_values weight_values next_values
        u v w)) /\
  (forall u v w1 w2,
    forward_star_edge head_values to_values weight_values next_values
      u v w1 ->
    forward_star_edge head_values to_values weight_values next_values
      u v w2 ->
    w1 = w2) /\
  forward_star_chain_wf head_values to_values next_values.

Module GraphForwardStar.

Definition store_graph
    (g : DijkstraGraph.G) (edge_count : Z)
    (head to weight next : addr) : Assertion :=
  EX head_values : list Z,
  EX to_values : list Z,
  EX weight_values : list Z,
  EX next_values : list Z,
    “ forward_star_model
        g edge_count head_values to_values weight_values next_values ” &&
    IntArray.full head (DijkstraGraph.vertex_count g) head_values **
    IntArray.full to edge_count to_values **
    IntArray.full weight edge_count weight_values **
    IntArray.full next edge_count next_values.

End GraphForwardStar.

Definition graph_dist_model
    (g : DijkstraGraph.G) (dist_values : list Z) (s : state) : Prop :=
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  forall v,
    vertex_valid g v ->
    dist_cell dist_values v = distance_as_cell (@dist Z s v).

Definition visited_set_empty (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

Definition visited_set_add
    (visited_set : Z -> Prop) (u : Z) (visited_set' : Z -> Prop) : Prop :=
  forall v, visited_set' v <-> visited_set v \/ v = u.

Definition visited_set_valid
    (g : DijkstraGraph.G) (visited_set : Z -> Prop) : Prop :=
  forall v, visited_set v -> vertex_valid g v.

Definition graph_state_invalid_default
    (g : DijkstraGraph.G) (s : state) : Prop :=
  forall v,
    ~ vertex_valid g v ->
    @dist Z s v = None /\ ~ @visited Z s v.

Definition graph_state_model
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (s : state) : Prop :=
  graph_dist_model g dist_values s /\
  (forall v,
    vertex_valid g v ->
    (visited_set v <-> @visited Z s v)) /\
  graph_state_invalid_default g s.

Definition set_state_visited (u : Z) (s : state) : state :=
  s <| visited ::= fun vs => vs ∪ [u] |>.

Definition dijkstra_init_dist
    (vertex_count src : Z) (dist_values : list Z) : Prop :=
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  0 < vertex_count <= DijkstraGraph.max_vertices /\
  0 <= src < vertex_count /\
  forall v,
    0 <= v < vertex_count ->
    dist_cell dist_values v =
      if Z.eq_dec v src then 0 else DijkstraGraph.infinity.

Definition initial_dist_values (src : Z) : list Z :=
  replace_Znth src 0
    (repeat DijkstraGraph.infinity
      (Z.to_nat DijkstraGraph.max_vertices)).

Definition dijkstra_shortest_dist
    (g : DijkstraGraph.G) (src : Z) (dist_values : list Z) : Prop :=
  exists s : state,
    graph_dist_model g dist_values s /\
    dijkstra_distance_correct g src s.

Fixpoint priority_queue_ordered (items : list (Z * Z)) : Prop :=
  match items with
  | nil => True
  | item :: items_tail =>
      (forall item0, In item0 items_tail -> fst item <= fst item0) /\
      priority_queue_ordered items_tail
  end.

Definition priority_queue_refines_unvisited_dist
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (items : list (Z * Z)) : Prop :=
  (forall v,
    vertex_valid g v ->
    ~ visited_set v ->
    dist_cell dist_values v < DijkstraGraph.infinity ->
    In (dist_cell dist_values v, v) items) /\
  (forall d v,
    In (d, v) items ->
    d = dist_cell dist_values v ->
    ~ visited_set v) /\
  (forall d v,
    In (d, v) items ->
    dist_cell dist_values v <= d) /\
  (forall d v, In (d, v) items -> d < DijkstraGraph.infinity) /\
  NoDup items.

Definition priority_queue_vertices_valid
    (g : DijkstraGraph.G) (items : list (Z * Z)) : Prop :=
  forall item,
    In item items ->
    vertex_valid g (snd item).

(** Basic loop-state predicates.

    These are intentionally placed immediately after the graph/dist/queue
    models they depend on.  They are lightweight safety and bridge states used
    by generated VCs before the later shortest-path mathematics enters. *)

Definition dijkstra_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z)
    (queue_items : list (Z * Z)) : Prop :=
  DijkstraGraph.graph_wf g /\
  vertex_valid g src /\
  nonnegative_edges g /\
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  priority_queue_ordered queue_items /\
  priority_queue_vertices_valid g queue_items.

Definition dijkstra_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_items : list (Z * Z)) : Prop :=
  dijkstra_loop_state g src visited_set dist_values queue_items /\
  priority_queue_refines_unvisited_dist g visited_set dist_values queue_items.

Definition state_distance_cell (v : Z) (s : state) : Z :=
  distance_as_cell (@dist Z s v).

Definition set_state_distance (v distance : Z) (s : state) : state :=
  @mkSt Z
    (@visited Z s)
    (fun u =>
      if Z.eq_dec u v then cell_as_distance distance else @dist Z s u).

Definition vertex_valid_dec
    (g : DijkstraGraph.G) (v : Z) : {vertex_valid g v} + {~ vertex_valid g v}.
Proof.
  unfold vertex_valid, DijkstraGraph.vertex_valid.
  destruct (Z_le_dec 0 v) as [Hlo | Hlo].
  - destruct (Z_lt_dec v (DijkstraGraph.vertex_count g)) as [Hhi | Hhi].
    + left. lia.
    + right. lia.
  - right. lia.
Defined.

Definition dijkstra_array_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) : state :=
  @mkSt Z
    (fun v => vertex_valid g v /\ visited_set v)
    (fun v =>
      if vertex_valid_dec g v
      then cell_as_distance (dist_cell dist_values v)
      else None).

Definition dijkstra_math_invariant
    (g : DijkstraGraph.G) (src : Z)
    (visited_set : Z -> Prop) (dist_values : list Z) : Prop :=
  dijkstra_visited_dist_final g src
    (dijkstra_array_state g visited_set dist_values) /\
  dijkstra_unvisited_dist_optimal g src
    (dijkstra_array_state g visited_set dist_values) /\
  dijkstra_visited_le_unvisited
    (dijkstra_array_state g visited_set dist_values).

Definition dijkstra_selected_min
    (g : DijkstraGraph.G)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (cur_vertex : Z) : Prop :=
  min_object_of_subset Z_op_le
    (fun v => @unvisited Z
      (dijkstra_array_state g visited_set dist_values) v)
    (@dist Z (dijkstra_array_state g visited_set dist_values))
    cur_vertex.

Definition dijkstra_after_visit_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (cur_vertex : Z) : state :=
  set_state_visited cur_vertex
    (dijkstra_array_state g visited_set dist_values).

Definition dijkstra_edge_math_state
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex : Z) (base_dist_values : list Z)
    (done : DijkstraGraph.E -> Prop) (dist_values : list Z) : Prop :=
  visited_set_add visited_before cur_vertex visited_after /\
  dijkstra_math_invariant g src visited_before base_dist_values /\
  dijkstra_selected_min g visited_before base_dist_values cur_vertex /\
    dijkstra_relax_step_invariant g cur_vertex
    (dijkstra_after_visit_state
      g visited_before base_dist_values cur_vertex)
    done
    (dijkstra_array_state g visited_after dist_values).

Section EdgeMathRelaxProofs.

Context (g : DijkstraGraph.G)
        (vertex_count src : Z)
        (visited_before visited_after : Z -> Prop)
        (cur_vertex : Z)
        (base_dist_values : list Z)
        (done : DijkstraGraph.E -> Prop)
        (dist_values : list Z)
        (edge : DijkstraGraph.E)
        (neighbor edge_weight cur_distance candidate : Z).

End EdgeMathRelaxProofs.

Definition forward_star_outgoing_edge_set
    (head_values to_values weight_values next_values : list Z)
    (u : Z) (e : DijkstraGraph.E) : Prop :=
  exists v w,
    e = (u, v) /\
    forward_star_edge head_values to_values weight_values next_values
      u v w.

Definition forward_star_suffix_index
    (next_values : list Z) (edge : Z) (idx : Z) : Prop :=
  edge <> -1 /\ next_chain next_values edge idx.

Definition forward_star_suffix_edge_set
    (to_values weight_values next_values : list Z)
    (u edge : Z) (e : DijkstraGraph.E) : Prop :=
  exists idx v w,
    forward_star_suffix_index next_values edge idx /\
    e = (u, v) /\
    0 <= idx < Zlength to_values /\
    Znth idx to_values 0 = v /\
    Znth idx weight_values 0 = w.

Definition forward_star_done_edge_set
    (head_values to_values weight_values next_values : list Z)
    (u edge : Z) (e : DijkstraGraph.E) : Prop :=
  forward_star_outgoing_edge_set
    head_values to_values weight_values next_values u e /\
  ~ forward_star_suffix_edge_set
    to_values weight_values next_values u edge e.

Definition dijkstra_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_items : list (Z * Z)) : Prop :=
  dijkstra_loop_bridge_state g src visited_set dist_values queue_items /\
  visited_set_valid g visited_set /\
  dijkstra_math_invariant g src visited_set dist_values.

Definition dijkstra_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (queue_items : list (Z * Z)) (s : state) : Prop :=
  exists visited_set dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_loop_math_bridge_state
      g src visited_set dist_values queue_items.

Definition source_visited_set (src : Z) : Z -> Prop :=
  fun v => v = src.

Definition dijkstra_first_step_math_state
    (g : DijkstraGraph.G) (src : Z)
    (done : DijkstraGraph.E -> Prop)
    (dist_values : list Z) : Prop :=
  dijkstra_first_step_invariant g src done
    (dijkstra_array_state g (source_visited_set src) dist_values).

End DijkstraLinkedForwardStar.
(* ---- end of the former common_helper_lib.v ---- *)
Require Import PVbench.Data_structures.priority_queue_index.rocq.spec_lib.

Export MonadNotation.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope sac.

Import DijkstraGraph.
Import DijkstraLinkedForwardStar.

Module DijkstraIndexQueue.

Definition index_queue_push_result
    (before after : multiset (Z * Z)) (vertex distance : Z) : Prop :=
  after = multiset_insert before (heap_item distance vertex).

Definition index_queue_pop_result
    (before after : multiset (Z * Z)) (vertex distance : Z) : Prop :=
  exists popped,
    popped = heap_item distance vertex /\
    multiset_minimum before popped /\
    after = multiset_remove before popped.

Definition heap_queue_items_valid
    (g : DijkstraGraph.G) (queue_set : multiset (Z * Z)) : Prop :=
  forall item,
    In item (mlist queue_set) ->
    vertex_valid g (item_data item) /\
    0 <= item_key item <= DijkstraGraph.infinity.

Definition heap_queue_refines_unvisited_dist
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  priority_queue_refines_unvisited_dist
    g visited_set dist_values (mlist queue_set).

Definition heap_queue_capacity
    (edge_count : Z) (queue_set : multiset (Z * Z)) : Prop :=
  multiset_size queue_set <= edge_count + 1.

Definition heap_queue_has_push_room
    (edge_count : Z) (queue_set : multiset (Z * Z)) : Prop :=
  multiset_size queue_set < edge_count + 1.

Definition heap_queue_capacity_budget
    (edge_count : Z) (queue_set : multiset (Z * Z)) : Prop :=
  0 <= edge_count /\
  heap_queue_capacity edge_count queue_set.

Definition processed_edge_budget
    (edge_count : Z) (processed_edges : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  0 <= edge_count /\
  NoDup processed_edges /\
  Forall (edge_index edge_count) processed_edges /\
  multiset_size queue_set <= Zlength processed_edges + 1.

Definition forward_star_suffix_fresh
    (next_values : list Z) (edge : Z)
    (processed_edges : list Z) : Prop :=
  forall idx,
    next_chain next_values edge idx ->
    ~ In idx processed_edges.

Definition forward_star_unvisited_fresh
    (head_values next_values : list Z)
    (visited_set : Z -> Prop)
    (processed_edges : list Z) : Prop :=
  forall u idx,
    storage_index u ->
    ~ visited_set u ->
    next_chain next_values (Znth u head_values (-1)) idx ->
    ~ In idx processed_edges.

Definition forward_star_chains_disjoint
    (head_values next_values : list Z) : Prop :=
  forall u1 u2 idx,
    storage_index u1 ->
    storage_index u2 ->
    next_chain next_values (Znth u1 head_values (-1)) idx ->
    next_chain next_values (Znth u2 head_values (-1)) idx ->
    u1 = u2.

Definition vertex_pair_valid (g : DijkstraGraph.G) (pair : Z * Z) : Prop :=
  vertex_valid g (fst pair) /\ vertex_valid g (snd pair).

Definition vertex_pair_code (pair : Z * Z) : Z :=
  fst pair * DijkstraGraph.max_vertices + snd pair.

Definition processed_vertex_pair_budget
    (g : DijkstraGraph.G) (processed_pairs : list (Z * Z))
    (queue_set : multiset (Z * Z)) : Prop :=
  NoDup processed_pairs /\
  Forall (vertex_pair_valid g) processed_pairs /\
  multiset_size queue_set <= Zlength processed_pairs + 1.

Definition processed_vertex_pairs_from_visited
    (visited_set : Z -> Prop) (processed_pairs : list (Z * Z)) : Prop :=
  forall u v,
    In (u, v) processed_pairs ->
    visited_set u.

Definition forward_star_pair_suffix_fresh
    (cur_vertex : Z) (to_values next_values : list Z) (edge : Z)
    (processed_pairs : list (Z * Z)) : Prop :=
  forall idx,
    next_chain next_values edge idx ->
    ~ In (cur_vertex, Znth idx to_values 0) processed_pairs.

Definition heap_queue_loop_capacity_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (queue_set : multiset (Z * Z)) : Prop :=
  exists processed_pairs,
    processed_vertex_pair_budget g processed_pairs queue_set /\
    processed_vertex_pairs_from_visited visited_set processed_pairs.

Definition heap_queue_edge_capacity_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (cur_vertex edge : Z)
    (head_values to_values next_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  visited_set cur_vertex /\
  (edge = -1 \/
    next_chain next_values (Znth cur_vertex head_values (-1)) edge) /\
  exists processed_pairs,
    processed_vertex_pair_budget g processed_pairs queue_set /\
    processed_vertex_pairs_from_visited visited_set processed_pairs /\
    forward_star_pair_suffix_fresh
      cur_vertex to_values next_values edge processed_pairs.

Definition dijkstra_heap_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  DijkstraGraph.graph_wf g /\
  vertex_valid g src /\
  nonnegative_edges g /\
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  heap_queue_items_valid g queue_set.

Definition dijkstra_heap_edge_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_loop_state g src visited_set dist_values queue_set /\
  vertex_valid g cur_vertex /\
  dist_cell dist_values cur_vertex = cur_distance /\
  -1 <= edge.

Definition dijkstra_heap_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_loop_state g src visited_set dist_values queue_set /\
  heap_queue_refines_unvisited_dist
    g visited_set dist_values queue_set.

Definition dijkstra_heap_after_pop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z)
    (queue_set_before queue_set_after : multiset (Z * Z))
    (cur_vertex cur_distance : Z) : Prop :=
  dijkstra_heap_loop_state g src visited_set dist_values queue_set_after /\
  heap_queue_refines_unvisited_dist
    g visited_set dist_values queue_set_before /\
  index_queue_pop_result
    queue_set_before queue_set_after cur_vertex cur_distance.

Definition dijkstra_heap_edge_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_edge_loop_state
    g src visited_set cur_vertex cur_distance edge dist_values queue_set /\
  heap_queue_refines_unvisited_dist
    g visited_set dist_values queue_set.

Definition index_queue_pop_choice
    (queue_set : multiset (Z * Z))
    : program state ((multiset (Z * Z) * Z) * Z) :=
  get (fun _ result =>
    index_queue_pop_result
      queue_set
      (fst (fst result))
      (snd (fst result))
      (snd result)).

Definition index_queue_push_choice
    (queue_set : multiset (Z * Z)) (vertex distance : Z)
    : program state (multiset (Z * Z)) :=
  get (fun _ queue_set_after =>
    index_queue_push_result queue_set queue_set_after vertex distance).

Definition dijkstra_heap_lfs_edge_body
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (acc : Z * multiset (Z * Z))
    : program state
        (CntOrBrk (Z * multiset (Z * Z)) (multiset (Z * Z))) :=
  let edge := fst acc in
  let queue_set := snd acc in
  choice
    (assume (fun _ => edge = -1);;
     ret (by_break queue_set))
    (assume (fun _ => edge <> -1);;
     let neighbor := Znth edge to_values 0 in
     let edge_weight := Znth edge weight_values 0 in
     let candidate := cur_distance + edge_weight in
     let next_edge := Znth edge next_values 0 in
     choice
       (assume (fun s =>
          0 <= edge_weight /\
          cur_distance <= DijkstraGraph.infinity - edge_weight /\
          candidate < state_distance_cell neighbor s);;
        update' (set_state_distance neighbor candidate);;
        queue_set_after <-
          index_queue_push_choice queue_set neighbor candidate;;
        ret (by_continue (next_edge, queue_set_after)))
       (assume (fun s =>
          edge_weight < 0 \/
          cur_distance > DijkstraGraph.infinity - edge_weight \/
          candidate >= state_distance_cell neighbor s);;
        ret (by_continue (next_edge, queue_set)))).

Definition dijkstra_heap_lfs_edge_loop
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (queue_set : multiset (Z * Z))
    : program state (multiset (Z * Z)) :=
  repeat_break
    (dijkstra_heap_lfs_edge_body
      head_values to_values weight_values next_values
      cur_vertex cur_distance)
    (edge, queue_set).

Definition dijkstra_heap_lfs_loop_body
    (head_values to_values weight_values next_values : list Z)
    (queue_set : multiset (Z * Z))
    : program state (CntOrBrk (multiset (Z * Z)) unit) :=
  choice
    (assume (fun _ => mlist queue_set = nil);;
     ret (by_break tt))
    (assume (fun _ => mlist queue_set <> nil);;
     pop_result <- index_queue_pop_choice queue_set;;
     let queue_set_after := fst (fst pop_result) in
     let cur_vertex := snd (fst pop_result) in
     let cur_distance := snd pop_result in
     choice
      (assume (fun s =>
         cur_distance = state_distance_cell cur_vertex s);;
        update' (set_state_visited cur_vertex);;
        queue_set_after_edges <-
          dijkstra_heap_lfs_edge_loop
            head_values to_values weight_values next_values
            cur_vertex cur_distance
            (Znth cur_vertex head_values 0)
            queue_set_after;;
        ret (by_continue queue_set_after_edges))
       (assume (fun s =>
          cur_distance <> state_distance_cell cur_vertex s);;
        ret (by_continue queue_set_after))).

Definition dijkstra_heap_lfs_loop
    (head_values to_values weight_values next_values : list Z)
    (queue_set : multiset (Z * Z)) : program state unit :=
  repeat_break
    (dijkstra_heap_lfs_loop_body
      head_values to_values weight_values next_values)
    queue_set.

Definition singleton_source_queue (src : Z) : multiset (Z * Z) :=
  multiset_insert (list_to_multiset (@nil (Z * Z))) (heap_item 0 src).

Definition dijkstra_heap_lfs_program
    (src : Z)
    (head_values to_values weight_values next_values : list Z)
    : program state unit :=
  dijkstra_heap_lfs_loop head_values to_values weight_values next_values
    (singleton_source_queue src).

Definition dijkstra_heap_loop_phase_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  (visited_set_empty visited_set /\
   dijkstra_init_dist (DijkstraGraph.vertex_count g) src dist_values /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   queue_set = singleton_source_queue src) \/
  (visited_set_valid g visited_set /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   dijkstra_math_invariant g src visited_set dist_values).

Definition dijkstra_heap_edge_phase_state
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  0 <= cur_distance < DijkstraGraph.infinity /\
  (((forall v, visited_set v <-> v = src) /\
    shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
    cur_vertex = src /\
    cur_distance = 0 /\
    (edge = -1 \/ next_chain next_values (Znth src head_values (-1)) edge) /\
    dijkstra_first_step_math_state
      g src
      (forward_star_done_edge_set
        head_values to_values weight_values next_values src edge)
      dist_values) \/
   (exists visited_before base_dist_values,
     visited_set_valid g visited_before /\
     shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
     visited_set_add visited_before cur_vertex visited_set /\
     cur_distance = dist_cell base_dist_values cur_vertex /\
     (edge = -1 \/ next_chain next_values (Znth cur_vertex head_values (-1)) edge) /\
     dijkstra_edge_math_state g src visited_before visited_set
       cur_vertex base_dist_values
       (forward_star_done_edge_set
         head_values to_values weight_values next_values cur_vertex edge)
       dist_values)).

Definition dijkstra_heap_lfs_edge_loop_after_body_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (step_result :
      CntOrBrk (Z * multiset (Z * Z)) (multiset (Z * Z)))
    : program state unit :=
  queue_set_after <-
    match step_result with
    | by_continue edge_state =>
        repeat_break
          (dijkstra_heap_lfs_edge_body
            head_values to_values weight_values next_values
            cur_vertex cur_distance)
          edge_state
    | by_break queue_set_done => ret queue_set_done
    end;;
  dijkstra_heap_lfs_loop
    head_values to_values weight_values next_values
    queue_set_after.

Definition dijkstra_heap_lfs_edge_loop_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (queue_set : multiset (Z * Z)) : program state unit :=
  queue_set_after <-
    dijkstra_heap_lfs_edge_loop
      head_values to_values weight_values next_values
      cur_vertex cur_distance edge queue_set;;
  dijkstra_heap_lfs_loop
    head_values to_values weight_values next_values
    queue_set_after.

Definition dijkstra_heap_lfs_after_pop_cont
    (head_values to_values weight_values next_values : list Z)
    (queue_set_after : multiset (Z * Z))
    (cur_vertex cur_distance : Z) : program state unit :=
  step_result <-
    choice
      (assume (fun s =>
         cur_distance = state_distance_cell cur_vertex s);;
       update' (set_state_visited cur_vertex);;
       queue_set_after_edges <-
         dijkstra_heap_lfs_edge_loop
           head_values to_values weight_values next_values
           cur_vertex cur_distance
           (Znth cur_vertex head_values 0)
           queue_set_after;;
       ret (by_continue queue_set_after_edges))
      (assume (fun s =>
         cur_distance <> state_distance_cell cur_vertex s);;
       ret (by_continue queue_set_after));;
  match step_result with
  | by_continue queue_set_next =>
      dijkstra_heap_lfs_loop
        head_values to_values weight_values next_values
        queue_set_next
  | by_break done => ret done
  end.

Definition dijkstra_heap_loop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_heap_lfs_loop head_values to_values weight_values next_values
      queue_set)
    X /\
  heap_queue_loop_capacity_state g visited_set queue_set /\
  heap_queue_refines_unvisited_dist g visited_set dist_values queue_set /\
  dijkstra_heap_loop_phase_state g src visited_set dist_values queue_set.

Definition dijkstra_heap_after_pop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set_after : multiset (Z * Z)) (cur_vertex cur_distance : Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_heap_lfs_after_pop_cont head_values to_values weight_values
      next_values queue_set_after cur_vertex cur_distance)
    X /\
  heap_queue_loop_capacity_state g visited_set queue_set_after /\
  exists queue_set_before,
    dijkstra_heap_loop_state g src visited_set dist_values queue_set_before /\
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set_before /\
    index_queue_pop_result
      queue_set_before queue_set_after cur_vertex cur_distance /\
    dijkstra_heap_loop_phase_state
      g src visited_set dist_values queue_set_before.

Definition dijkstra_heap_edge_loop_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_heap_lfs_edge_loop_cont head_values to_values weight_values
      next_values cur_vertex cur_distance edge queue_set)
    X /\
  heap_queue_edge_capacity_state
    g visited_set cur_vertex edge head_values to_values next_values
    queue_set /\
  heap_queue_refines_unvisited_dist g visited_set dist_values queue_set /\
  dijkstra_heap_edge_phase_state
    g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values queue_set.

Definition dijkstra_heap_lfs_initial_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (eq (initial_state src))
    (dijkstra_heap_lfs_program
      src head_values to_values weight_values next_values)
    X /\
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Definition dijkstra_heap_after_relax_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge
       neighbor candidate : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (queue_set_after <-
       index_queue_push_choice queue_set neighbor candidate;;
     dijkstra_heap_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance
       (Znth edge next_values 0) queue_set_after)
    X /\
  heap_queue_edge_capacity_state
    g visited_set cur_vertex edge head_values to_values next_values
    queue_set /\
  forall queue_set_after,
    index_queue_push_result queue_set queue_set_after neighbor candidate ->
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set_after /\
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values queue_set_after.

Definition dijkstra_heap_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_loop_bridge_state g src visited_set dist_values queue_set /\
  visited_set_valid g visited_set /\
  dijkstra_math_invariant g src visited_set dist_values.

Definition dijkstra_heap_edge_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (base_dist_values dist_values : list Z)
    (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z) : Prop :=
  dijkstra_heap_edge_loop_bridge_state
    g src visited_after cur_vertex cur_distance edge dist_values queue_set /\
  visited_set_valid g visited_before /\
  visited_set_add visited_before cur_vertex visited_after /\
  cur_distance = dist_cell base_dist_values cur_vertex /\
  (edge = -1 \/ next_chain next_values (Znth cur_vertex head_values (-1)) edge) /\
  dijkstra_edge_math_state g src visited_before visited_after
    cur_vertex base_dist_values
    (forward_star_done_edge_set
      head_values to_values weight_values next_values cur_vertex edge)
    dist_values.

Definition dijkstra_heap_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (queue_set : multiset (Z * Z)) (s : state) : Prop :=
  exists visited_set dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_heap_loop_math_bridge_state
      g src visited_set dist_values queue_set.

Definition dijkstra_heap_edge_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (base_dist_values : list Z) (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g visited_after dist_values s /\
    0 <= cur_distance < DijkstraGraph.infinity /\
    dijkstra_heap_edge_loop_math_bridge_state
      g src visited_before visited_after cur_vertex cur_distance edge
      base_dist_values dist_values queue_set
      head_values to_values weight_values next_values.

Definition dijkstra_heap_first_edge_loop_math_bridge_state
    (g : DijkstraGraph.G) (src edge : Z)
    (dist_values : list Z) (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z) : Prop :=
  dijkstra_heap_edge_loop_bridge_state
    g src (source_visited_set src) src 0 edge dist_values queue_set /\
  (edge = -1 \/ next_chain next_values (Znth src head_values (-1)) edge) /\
  dijkstra_first_step_math_state
    g src
    (forward_star_done_edge_set
      head_values to_values weight_values next_values src edge)
    dist_values.

Definition dijkstra_heap_first_edge_loop_math_model
    (g : DijkstraGraph.G) (src edge : Z)
    (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g (source_visited_set src) dist_values s /\
    dijkstra_heap_first_edge_loop_math_bridge_state
      g src edge dist_values queue_set
      head_values to_values weight_values next_values.

Section HeapFirstStepProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hsrc : vertex_valid g src.
Hypothesis Hnonneg : nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow :
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Local Notation done_edges :=
  (forward_star_done_edge_set
    head_values to_values weight_values next_values).

End HeapFirstStepProofs.

Section HeapLoopMathProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hnonneg : nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow :
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Local Notation done_edges :=
  (forward_star_done_edge_set
    head_values to_values weight_values next_values).

End HeapLoopMathProofs.

Section HeapProgramProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hsrc : vertex_valid g src.
Hypothesis Hnonneg : nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow :
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Local Notation done_edges :=
  (forward_star_done_edge_set
    head_values to_values weight_values next_values).

End HeapProgramProofs.

End DijkstraIndexQueue.
