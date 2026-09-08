Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Require Import Algorithms.DFS.DFS.
Require Import GraphLib.reachable.reachable_basic.
Require Import PVbench.Algorithms.DFS_adjacency_list.rocq.spec_lib.

Import ListNotations.
Import MonadNotation.
Import PVbench.Algorithms.DFS_adjacency_list.rocq.spec_lib.DFSAdjacencyList.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition applyf {A B : Type} (f : A -> B) (a : A) : B := f a.

Module DFSAdjacencyList.

(** Annotation-facing specialization: [E] is not determined by [G] and [V],
    so Rocq cannot infer the concrete [Graph G V E] instance from [DFS g u]. *)
Definition dfs_program
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  @DFS ZSimpleGraph.G Z ZSimpleGraph.E ZSimpleGraph.graph_instance g u.

Definition dfs_step
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @step ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g u v.

Definition dfs_loop
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  whileP
    (fun visited_set => exists v, dfs_step g u v /\ ~ visited_set v)
    (v <- get (fun visited_set v =>
      dfs_step g u v /\ ~ visited_set v);;
     dfs_program g v).

Definition dfs_continue
    (g : ZSimpleGraph.G) (u : Z) (_ : unit)
    : program (Z -> Prop) unit :=
  dfs_loop g u.

Fixpoint addressed_sllseg
    (cursor stop : addr) (node_addrs : list addr) (values : list Z)
    : Assertion :=
  match node_addrs, values with
  | nil, nil => “ cursor = stop ” && emp
  | node :: node_addrs', datum :: values' =>
      “ cursor = node /\ node <> NULL ” &&
      EX next : addr,
        &(node # "list" ->ₛ "data") # Int |-> datum **
        &(node # "list" ->ₛ "next") # Ptr |-> next **
        addressed_sllseg next stop node_addrs' values'
  | _, _ => “ False ”
  end.

Definition list_blocks_missing
    (u : Z) (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) : Assertion :=
  iter_sepcon
    (map row_block
      (PtrPtrArray2.remove_Znth u
        (combine row_ptrs (combine node_addrs rows)))).

Definition all_visited
    (vertices : list Z) (visited_set : Z -> Prop) : Prop :=
  forall v, In v vertices -> visited_set v.

(** A DFS call only adds vertices to the caller's visited set. *)
Definition visited_extension
    (before after : Z -> Prop) : Prop :=
  forall v, before v -> after v.

(** The immutable graph representation with row [u] removed.  The caller
    separately owns the pointer-array cell and the split linked-list row. *)
Definition graph_except
    (adjacency : addr) (g : ZSimpleGraph.G)
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) (u : Z)
    : Assertion :=
  “ adjacency_lists_model g rows /\
    Zlength row_ptrs = ZSimpleGraph.vertex_count g /\
    Zlength node_addrs = ZSimpleGraph.vertex_count g /\
    Zlength rows = ZSimpleGraph.vertex_count g /\
    ZSimpleGraph.vertex_valid g u ” &&
  PtrArray.missing_i
    adjacency u 0 (ZSimpleGraph.vertex_count g) row_ptrs **
  list_blocks_missing u row_ptrs node_addrs rows.

End DFSAdjacencyList.
