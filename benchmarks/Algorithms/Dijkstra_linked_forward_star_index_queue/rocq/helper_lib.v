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
Require Export PVbench.Algorithms.Dijkstra_linked_forward_star_index_queue.rocq.common_helper_lib.
Require Import PVbench.Algorithms.Dijkstra_linked_forward_star_index_queue.rocq.priority_queue_helper_lib.

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
