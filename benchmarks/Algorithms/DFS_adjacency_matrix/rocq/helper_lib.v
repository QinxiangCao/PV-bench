Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.SL Require Import GraphLib.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Require Export PVbench.Algorithms.DFS_adjacency_matrix.rocq.spec_lib.
Require Import GraphLib.reachable.reachable_basic.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Require Import Algorithms.DFS.DFS.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.
Import naive_C_Rules.
Local Open Scope sac.

Module DFSAdjacencyMatrixGraphLib.
  Include GraphLibSig
    Arch32 BigEndian
    naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules
    naive_C_Rules.
End DFSAdjacencyMatrixGraphLib.

(** Annotation-facing application combinator used by generated refinement
    obligations. *)
Definition applyf {A B : Type} (f : A -> B) (a : A) : B := f a.

Module DFSAdjacencyMatrix.

Module BooleanGraph <: DFSAdjacencyMatrixGraphLib.BOOLEAN_MATRIX_GRAPH.
  Definition G : Type := ZSimpleGraph.G.
  Definition vertex_count : G -> Z := ZSimpleGraph.vertex_count.
  Definition graph_wf : G -> Prop := ZSimpleGraph.graph_wf.
  Definition vertex_valid : G -> Z -> Prop := ZSimpleGraph.vertex_valid.
  Definition graph_step : G -> Z -> Z -> Prop := ZSimpleGraph.graph_step.

  Lemma vertex_valid_count :
    forall g v,
      graph_wf g ->
      vertex_valid g v ->
      DFSAdjacencyMatrixGraphLib.vertex_index (vertex_count g) v.
  Proof.
    intros g v _ Hv.
    exact Hv.
  Qed.
End BooleanGraph.

Module MatrixGraph :=
  DFSAdjacencyMatrixGraphLib.BooleanIntMatrixGraphModelLib BooleanGraph.

Definition matrix_layout
    (g : ZSimpleGraph.G) (rows : list (list Z))
    : DFSAdjacencyMatrixGraphLib.IntMatrixLayoutStore.Layout :=
  DFSAdjacencyMatrixGraphLib.mkMatrixLayout
    Z (ZSimpleGraph.vertex_count g) rows.

(** Annotation-facing specialization: [E] is not determined by [G] and [V],
    so Rocq cannot infer the concrete [Graph G V E] instance from [DFS g u]. *)
Definition dfs_program
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  @DFS
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g u.

(** Annotation-facing specialization of graph reachability. *)
Definition graph_reachable
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @reachable
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance
    g u v.

(** The loop left after the initial visit performed by [dfs_program]. *)
Definition dfs_loop
    (g : ZSimpleGraph.G) (source : Z) : program (Z -> Prop) unit :=
  whileP
    (fun visited_set =>
      exists neighbor,
        ZSimpleGraph.graph_step g source neighbor /\
        ~ visited_set neighbor)
    (neighbor <- get (fun visited_set neighbor =>
       ZSimpleGraph.graph_step g source neighbor /\
       ~ visited_set neighbor);;
     dfs_program g neighbor).

(** Continuation used when one recursive DFS call returns to the enclosing
    vertex's remaining abstract loop. *)
Definition dfs_continue
    (g : ZSimpleGraph.G) (source : Z)
    (_ : unit) : program (Z -> Prop) unit :=
  dfs_loop g source.

(** The source is visited, and every outgoing neighbor whose matrix column is
    already scanned is in the current abstract visited set. *)
Definition processed_neighbors
    (g : ZSimpleGraph.G) (source upto : Z)
    (visited_set : Z -> Prop) : Prop :=
  visited_set source /\
  forall v,
    0 <= v < upto ->
    ZSimpleGraph.graph_step g source v ->
    visited_set v.

(** DFS only adds vertices to the visited set. *)
Definition visited_extension
    (before after : Z -> Prop) : Prop :=
  forall v, before v -> after v.

(** The public entry point starts from an empty visited set.  Naming this
    predicate also keeps the annotation-level contract free of nested binders. *)
Definition empty_visited (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

(** Annotation-facing pure relation between a square 0/1 matrix and the graph.
    The short name is kept for generated goals; the definition is provided by
    [GraphLib]'s boolean integer matrix instance. *)
Definition adjacency_matrix_model
    (g : ZSimpleGraph.G) (rows : list (list Z)) : Prop :=
  MatrixGraph.model g (matrix_layout g rows).

Definition visited
    (visited_ptr : addr) (g : ZSimpleGraph.G) (visited_set : Z -> Prop)
    : Assertion :=
  EX values : list Z,
    “ ZSimpleGraph.visited_values g values visited_set ” &&
    IntArray.full visited_ptr (ZSimpleGraph.vertex_count g) values.

End DFSAdjacencyMatrix.
