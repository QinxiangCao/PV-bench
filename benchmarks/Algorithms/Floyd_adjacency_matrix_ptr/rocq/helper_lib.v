Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Require Export PVbench.Algorithms.Floyd_adjacency_matrix_ptr.rocq.spec_lib.
From MonadLib Require Import MonadLib.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelMonad.
From RecordUpdate Require Import RecordUpdate.
From MaxMinLib Require Import Interface.
Require Import Algorithms.MapLib.
Require Import Algorithms.Floyd.Floyd.
From GraphLib Require Import graph_basic path path_basic epath Zweight.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope map_scope.
Import naive_C_Rules.
Local Open Scope sac.

Module FloydAdjacencyMatrix2Darray.

Definition state : Type := @St Z.

Definition floyd_update_dist (i j k : Z) : program state unit :=
  @update_dist Z FloydGraph.edge_eqdec i j k.

Definition floyd_j_from
    (g : FloydGraph.G) (n k i j : Z) : program state unit :=
  range_iter j n
    (fun j _ => floyd_update_dist i j k)
    tt.

Definition floyd_i_from
    (g : FloydGraph.G) (n k i : Z) : program state unit :=
  range_iter i n
    (fun i _ => floyd_j_from g n k i 0)
    tt.

Definition floyd_k_from
    (g : FloydGraph.G) (n k : Z) : program state unit :=
  range_iter k n
    (fun k _ => floyd_i_from g n k 0)
    tt.

Definition floyd_k_after
    (g : FloydGraph.G) (n k : Z) : unit -> program state unit :=
  fun _ => floyd_k_from g n (k + 1).

Definition floyd_i_k_from
    (g : FloydGraph.G) (n k i : Z) : program state unit :=
  bind (floyd_i_from g n k i) (floyd_k_after g n k).

Definition floyd_i_k_after
    (g : FloydGraph.G) (n k i : Z) : unit -> program state unit :=
  fun _ => floyd_i_k_from g n k (i + 1).

Definition floyd_j_i_k_from
    (g : FloydGraph.G) (n k i j : Z) : program state unit :=
  bind (floyd_j_from g n k i j) (floyd_i_k_after g n k i).

Definition floyd_indexed_program
    (g : FloydGraph.G) (n : Z) : program state unit :=
  floyd_k_from g n 0.

Definition matrix_distance (rows : list (list Z)) (u v : Z) : option Z :=
  FloydGraph.matrix_distance rows u v.
 
(* function *)
Definition state_of_matrix (rows : list (list Z)) : state :=
  @mkSt Z (fun uv => matrix_distance rows (fst uv) (snd uv)).

Definition storage_index (i : Z) : Prop :=
  0 <= i < FloydGraph.max_vertices.

Definition physical_cell (rows : list (list Z)) (u v : Z) : Z :=
  Znth v (Znth u rows nil) FloydGraph.infinity.

(** Abstract Floyd distances are nonnegative.  [None] is infinity; a finite
    abstract value at or above the physical sentinel is observed as the same
    infinity cell. *)
Definition abstract_distance_nonnegative (d : option Z) : Prop :=
  match d with
  | Some z => 0 <= z
  | None => True
  end.

Definition distance_as_observed_cell (d : option Z) : Z :=
  match d with
  | Some z =>
      if Z_lt_dec z FloydGraph.infinity
      then z
      else FloydGraph.infinity
  | None => FloydGraph.infinity
  end.

(** Only valid physical matrix coordinates are observable.  This guard keeps
    [Znth]'s default/negative-index behavior outside the representation
    boundary, while exact finite values and saturated infinity remain related
    inside the fixed-capacity matrix. *)
Definition state_model (rows : list (list Z)) (s : state) : Prop :=
  forall u v,
    storage_index u ->
    storage_index v ->
    abstract_distance_nonnegative (@dist Z s (u, v)) /\
    physical_cell rows u v =
      distance_as_observed_cell (@dist Z s (u, v)).

Definition matrix_model (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  FloydGraph.matrix_graph_model g rows.

Definition matrix_shape (rows : list (list Z)) : Prop :=
  FloydGraph.matrix_shape FloydGraph.max_vertices rows.

Definition matrix_values_safe (rows : list (list Z)) : Prop :=
  forall i j,
    storage_index i ->
    storage_index j ->
    0 <= physical_cell rows i j <= FloydGraph.infinity.

Definition graph_storage_size (_ : FloydGraph.G) : Z :=
  FloydGraph.max_vertices.

Definition graph_matrix_model
    (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  matrix_model g rows /\
  matrix_shape rows /\
  matrix_values_safe rows.

Definition matrix_storage_size : Z :=
  FloydGraph.max_vertices.

Definition matrix_rows_model (rows : list (list Z)) : Prop :=
  matrix_shape rows /\ matrix_values_safe rows.

Definition valid_size (n : Z) : Prop :=
  0 <= n <= FloydGraph.max_vertices.

Definition graph_has_size (g : FloydGraph.G) (n : Z) : Prop :=
  FloydGraph.vertex_count g = n /\ valid_size n.

Definition floyd_no_negative_cycle
    (g : FloydGraph.G) : Prop :=
  forall u p,
    @valid_epath FloydGraph.G FloydGraph.V FloydGraph.E
      FloydGraph.graph_instance FloydGraph.gvalid_instance
      FloydGraph.PathData FloydGraph.path_instance g u p u ->
    Z_op_le (Some 0)
      (@epath_weight FloydGraph.G FloydGraph.E
        FloydGraph.weight_instance g p).

Definition floyd_nonnegative_edges
    (g : FloydGraph.G) : Prop :=
  forall e,
    FloydGraph.edge_valid g e ->
    Z_op_le (Some 0)
      (@weight FloydGraph.G FloydGraph.E
        FloydGraph.weight_instance g e).

Definition floyd_initial_state
    (g : FloydGraph.G) (s : state) : Prop :=
  @initialized_state FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance FloydGraph.gvalid_instance
    g FloydGraph.PathData FloydGraph.path_instance
    FloydGraph.weight_instance s.

Definition floyd_shortest_state
    (g : FloydGraph.G) (s : state) : Prop :=
  @distance_correct FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance FloydGraph.gvalid_instance
    g FloydGraph.PathData FloydGraph.path_instance
    FloydGraph.weight_instance s.

Definition floyd_init_matrix
    (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  floyd_initial_state g (state_of_matrix rows).

Definition floyd_shortest_matrix
    (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  matrix_shape rows /\
  matrix_values_safe rows /\
  exists s : state,
    state_model rows s /\
    floyd_shortest_state g s.

End FloydAdjacencyMatrix2Darray.

Section ForsetRangeIterRefinement.

Definition floyd_program
    (g : FloydGraph.G) : program FloydAdjacencyMatrix2Darray.state unit :=
  @Floyd FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance g FloydGraph.edge_eqdec.

Definition floyd_i_program
    (g : FloydGraph.G) (k i : Z)
    : program FloydAdjacencyMatrix2Darray.state unit :=
  @Floyd_i FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance g FloydGraph.edge_eqdec k i.

Definition floyd_k_program
    (g : FloydGraph.G) (k : Z)
    : program FloydAdjacencyMatrix2Darray.state unit :=
  @Floyd_k FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance g FloydGraph.edge_eqdec k.

End ForsetRangeIterRefinement.
