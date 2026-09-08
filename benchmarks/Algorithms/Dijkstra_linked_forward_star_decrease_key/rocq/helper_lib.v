Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.
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
Require Export PVbench.Algorithms.Dijkstra_linked_forward_star_decrease_key.rocq.common_helper_lib.
Require Import PVbench.Algorithms.Dijkstra_linked_forward_star_decrease_key.rocq.priority_queue_helper_lib.

Export MonadNotation.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope sac.

Import DijkstraGraph.
Import DijkstraLinkedForwardStar.

Module DijkstraDecreaseKey.

Definition partial_map_empty : partial_map := fun _ => None.

Definition partial_map_is_empty (M : partial_map) : Prop :=
  forall data_x key_x, ~ partial_map_present M data_x key_x.

Definition dk_map_queue_push_result
    (before after : partial_map) (vertex distance : Z) : Prop :=
  after = partial_map_add before vertex distance.

Definition dk_map_queue_pop_result
    (before after : partial_map) (vertex distance : Z) : Prop :=
  partial_map_minimum before (heap_item distance vertex) /\
  after = partial_map_remove before vertex.

Definition dk_map_queue_update_or_push_result
    (before after : partial_map)
    (size_before size_after vertex distance : Z) : Prop :=
  partial_map_update_or_add_size
    before size_before size_after vertex distance /\
  after = partial_map_update_or_add before vertex distance.

Definition dk_map_queue_update_or_push_result_any
    (before after : partial_map) (vertex distance : Z) : Prop :=
  exists size_before size_after,
    dk_map_queue_update_or_push_result
      before after size_before size_after vertex distance.

Definition map_queue_items_valid
    (g : DijkstraGraph.G) (M : partial_map) : Prop :=
  forall data_x key_x,
    partial_map_present M data_x key_x ->
    vertex_valid g data_x /\
    0 <= key_x <= DijkstraGraph.infinity.

Definition map_queue_exact_unvisited_dist
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  (forall data_x key_x,
    partial_map_present M data_x key_x ->
    vertex_valid g data_x /\
    ~ visited_set data_x /\
    key_x = dist_cell dist_values data_x /\
    0 <= key_x < DijkstraGraph.infinity) /\
  (forall v,
    vertex_valid g v ->
    ~ visited_set v ->
    dist_cell dist_values v < DijkstraGraph.infinity ->
    partial_map_present M v (dist_cell dist_values v)).

Definition dijkstra_dk_map_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  DijkstraGraph.graph_wf g /\
  vertex_valid g src /\
  nonnegative_edges g /\
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  map_queue_items_valid g M.

Definition dijkstra_dk_map_edge_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z) (dist_values : list Z)
    (M : partial_map) : Prop :=
  dijkstra_dk_map_loop_state g src visited_set dist_values M /\
  vertex_valid g cur_vertex /\
  dist_cell dist_values cur_vertex = cur_distance /\
  -1 <= edge.

Definition dk_map_queue_pop_choice
    (M : partial_map) : program state ((partial_map * Z) * Z) :=
  get (fun _ result =>
    dk_map_queue_pop_result
      M
      (fst (fst result))
      (snd (fst result))
      (snd result)).

Definition dk_map_queue_update_or_push_choice
    (M : partial_map) (vertex distance : Z)
    : program state partial_map :=
  get (fun _ M_after =>
    dk_map_queue_update_or_push_result_any
      M M_after vertex distance).

Definition dijkstra_dk_lfs_edge_body
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (acc : Z * partial_map)
    : program state
        (CntOrBrk (Z * partial_map) partial_map) :=
  let edge := fst acc in
  let M := snd acc in
  choice
    (assume (fun _ => edge = -1);;
     ret (by_break M))
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
        M_after <-
          dk_map_queue_update_or_push_choice M neighbor candidate;;
        ret (by_continue (next_edge, M_after)))
       (assume (fun s =>
          edge_weight < 0 \/
          cur_distance > DijkstraGraph.infinity - edge_weight \/
          candidate >= state_distance_cell neighbor s);;
        ret (by_continue (next_edge, M)))).

Definition dijkstra_dk_lfs_edge_loop
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (M : partial_map) : program state partial_map :=
  repeat_break
    (dijkstra_dk_lfs_edge_body
      head_values to_values weight_values next_values
      cur_vertex cur_distance)
    (edge, M).

Definition dijkstra_dk_lfs_loop_body
    (head_values to_values weight_values next_values : list Z)
    (M : partial_map)
    : program state (CntOrBrk partial_map unit) :=
  choice
    (assume (fun _ => partial_map_is_empty M);;
     ret (by_break tt))
    (assume (fun _ => ~ partial_map_is_empty M);;
     pop_result <- dk_map_queue_pop_choice M;;
     let M_after := fst (fst pop_result) in
     let cur_vertex := snd (fst pop_result) in
     let cur_distance := snd pop_result in
     update' (set_state_visited cur_vertex);;
     M_after_edges <-
       dijkstra_dk_lfs_edge_loop
         head_values to_values weight_values next_values
         cur_vertex cur_distance
         (Znth cur_vertex head_values 0)
         M_after;;
     ret (by_continue M_after_edges)).

Definition dijkstra_dk_lfs_loop
    (head_values to_values weight_values next_values : list Z)
    (M : partial_map) : program state unit :=
  repeat_break
    (dijkstra_dk_lfs_loop_body
      head_values to_values weight_values next_values)
    M.

Definition singleton_source_map (src : Z) : partial_map :=
  partial_map_add partial_map_empty src 0.

Definition dijkstra_dk_lfs_program
    (src : Z)
    (head_values to_values weight_values next_values : list Z)
    : program state unit :=
  dijkstra_dk_lfs_loop head_values to_values weight_values next_values
    (singleton_source_map src).

Definition dijkstra_dk_lfs_edge_loop_after_body_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (step_result :
      CntOrBrk (Z * partial_map) partial_map)
    : program state unit :=
  M_after <-
    match step_result with
    | by_continue edge_state =>
        repeat_break
          (dijkstra_dk_lfs_edge_body
            head_values to_values weight_values next_values
            cur_vertex cur_distance)
          edge_state
    | by_break M_done => ret M_done
    end;;
  dijkstra_dk_lfs_loop
    head_values to_values weight_values next_values
    M_after.

Definition dijkstra_dk_lfs_edge_loop_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (M : partial_map) : program state unit :=
  M_after <-
    dijkstra_dk_lfs_edge_loop
      head_values to_values weight_values next_values
      cur_vertex cur_distance edge M;;
  dijkstra_dk_lfs_loop
    head_values to_values weight_values next_values
    M_after.

Definition dijkstra_dk_lfs_after_pop_cont
    (head_values to_values weight_values next_values : list Z)
    (M_after : partial_map)
    (cur_vertex cur_distance : Z) : program state unit :=
  step_result <-
    (update' (set_state_visited cur_vertex);;
     M_after_edges <-
       dijkstra_dk_lfs_edge_loop
         head_values to_values weight_values next_values
         cur_vertex cur_distance
         (Znth cur_vertex head_values 0)
         M_after;;
     ret (by_continue M_after_edges));;
  match step_result with
  | by_continue M_next =>
      dijkstra_dk_lfs_loop
        head_values to_values weight_values next_values
        M_next
  | by_break done => ret done
  end.

Definition dijkstra_dk_map_loop_phase_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  (visited_set_empty visited_set /\
   dijkstra_init_dist (DijkstraGraph.vertex_count g) src dist_values /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   M = singleton_source_map src) \/
  (visited_set_valid g visited_set /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   dijkstra_math_invariant g src visited_set dist_values).

Definition dijkstra_dk_map_edge_phase_state
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (_M : partial_map) : Prop :=
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

Definition dijkstra_dk_map_loop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M : partial_map) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_dk_lfs_loop head_values to_values weight_values next_values M)
    X /\
  map_queue_exact_unvisited_dist g visited_set dist_values M /\
  dijkstra_dk_map_loop_phase_state g src visited_set dist_values M.

Definition dijkstra_dk_map_after_pop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M_after : partial_map) (cur_vertex cur_distance : Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_dk_lfs_after_pop_cont head_values to_values weight_values
      next_values M_after cur_vertex cur_distance)
    X /\
  exists M_before,
    dijkstra_dk_map_loop_state g src visited_set dist_values M_before /\
    map_queue_exact_unvisited_dist g visited_set dist_values M_before /\
    dk_map_queue_pop_result M_before M_after cur_vertex cur_distance /\
    dijkstra_dk_map_loop_phase_state
      g src visited_set dist_values M_before.

Definition dijkstra_dk_map_edge_loop_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M : partial_map) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_dk_lfs_edge_loop_cont head_values to_values weight_values
      next_values cur_vertex cur_distance edge M)
    X /\
  map_queue_exact_unvisited_dist g visited_set dist_values M /\
  dijkstra_dk_map_edge_phase_state
    g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values M.

Definition dijkstra_dk_lfs_initial_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (eq (initial_state src))
    (dijkstra_dk_lfs_program
      src head_values to_values weight_values next_values)
    X /\
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Definition dijkstra_dk_map_after_relax_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge
       neighbor candidate : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M : partial_map) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (M_after <-
       dk_map_queue_update_or_push_choice M neighbor candidate;;
     dijkstra_dk_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance
       (Znth edge next_values 0) M_after)
    X /\
  forall M_after,
    dk_map_queue_update_or_push_result_any
      M M_after neighbor candidate ->
    map_queue_exact_unvisited_dist
      g visited_set dist_values M_after /\
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values M_after.

Definition dijkstra_dk_map_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  dijkstra_dk_map_loop_state g src visited_set dist_values M /\
  map_queue_exact_unvisited_dist g visited_set dist_values M /\
  visited_set_valid g visited_set /\
  dijkstra_math_invariant g src visited_set dist_values.

Definition dijkstra_dk_map_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (M : partial_map) (s : state) : Prop :=
  exists visited_set dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_dk_map_loop_math_bridge_state
      g src visited_set dist_values M.

Definition dijkstra_dk_map_edge_loop_math_model
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (M : partial_map)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M /\
    map_queue_exact_unvisited_dist g visited_set dist_values M /\
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M.

Section DijkstraDecreaseKeyProgramProofs.

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

End DijkstraDecreaseKeyProgramProofs.

End DijkstraDecreaseKey.
