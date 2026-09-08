Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export PVbench.Algorithms.DFS_adjacency_matrix_2Darray.rocq.spec_lib.
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

Definition applyf {A B : Type} (f : A -> B) (a : A) : B := f a.

Module DFSAdjacencyMatrix2Darray.

Definition dfs_program
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  @DFS
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g u.

Definition graph_reachable
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @reachable
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance
    g u v.

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

Definition dfs_continue
    (g : ZSimpleGraph.G) (source : Z)
    (_ : unit) : program (Z -> Prop) unit :=
  dfs_loop g source.

Definition processed_neighbors
    (g : ZSimpleGraph.G) (source upto : Z)
    (visited_set : Z -> Prop) : Prop :=
  visited_set source /\
  forall v,
    0 <= v < upto ->
    ZSimpleGraph.graph_step g source v ->
    visited_set v.

Definition visited_extension
    (before after : Z -> Prop) : Prop :=
  forall v, before v -> after v.

Definition empty_visited (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

Definition adjacency_matrix_model
    (g : ZSimpleGraph.G) (rows : list (list Z)) : Prop :=
  ZSimpleGraph.graph_wf g /\
  Zlength rows = ZSimpleGraph.vertex_count g /\
  Forall
    (fun row => Zlength row = ZSimpleGraph.vertex_count g)
    rows /\
  forall u v,
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    let value := Znth v (Znth u rows nil) 0 in
    (value = 0 \/ value = 1) /\
    (value = 1 <-> ZSimpleGraph.graph_step g u v).

Definition store_graph
    (matrix : addr) (g : ZSimpleGraph.G) (rows : list (list Z))
    : Assertion :=
  “ adjacency_matrix_model g rows ” &&
  IntPtrArray2.full
    matrix
    (ZSimpleGraph.vertex_count g)
    rows.

Definition graph (matrix : addr) (g : ZSimpleGraph.G) : Assertion :=
  EX rows : list (list Z),
    store_graph matrix g rows.

Definition visited
    (visited_ptr : addr) (g : ZSimpleGraph.G) (visited_set : Z -> Prop)
    : Assertion :=
  EX values : list Z,
    “ ZSimpleGraph.visited_values g values visited_set ” &&
    IntArray.full visited_ptr (ZSimpleGraph.vertex_count g) values.

End DFSAdjacencyMatrix2Darray.

Require Import Coq.micromega.Lia.

