Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
From SumLib Require Import ZRange.

Local Open Scope Z_scope.

(** Dense integer-indexed simple directed graphs.  An edge is identified by
    its ordered pair of endpoints, so parallel edges are impossible. *)
Module ZSimpleGraph.

Definition V : Type := Z.
Definition E : Type := (Z * Z)%type.

Record G : Type := mkG {
  vertex_count : Z;
  adjacency : V -> V -> Prop;
}.

Definition vertex_valid (g : G) (v : V) : Prop :=
  0 <= v < vertex_count g.

Definition graph_step (g : G) (u v : V) : Prop :=
  vertex_valid g u /\
  vertex_valid g v /\
  adjacency g u v.
 
Definition edge_valid (g : G) (e : E) : Prop :=
  graph_step g (fst e) (snd e).

Definition graph_wf (g : G) : Prop :=
  0 <= vertex_count g /\
  forall v, vertex_valid g v -> ~ adjacency g v v.

Definition vertices (g : G) : list V :=
  Zrange 0 (vertex_count g).

(** Shared pure relation used by concrete DFS implementations whose visited
    set is stored as a dense 0/1 integer array. *)
Definition visited_values
    (g : G) (values : list Z) (visited_set : V -> Prop) : Prop :=
  Zlength values = vertex_count g /\
  (forall v, visited_set v -> vertex_valid g v) /\
  forall v,
    vertex_valid g v ->
    (Znth v values 0 = 0 \/ Znth v values 0 = 1) /\
    (visited_set v <-> Znth v values 0 = 1).

#[export] Instance graph_instance : Graph G V E := {|
  vvalid := vertex_valid;
  evalid := edge_valid;
  step_aux := fun g e u v => e = (u, v) /\ graph_step g u v;
|}.

#[export] Instance gvalid_instance : GValid G := graph_wf.

#[export] Instance stepvalid_instance : StepValid G V E.
Proof.
  constructor.
  - intros g e u v [_ [Hu _]]. exact Hu.
  - intros g e u v [_ [_ [Hv _]]]. exact Hv.
  - intros g e u v [-> Hstep].
    unfold edge_valid; simpl; exact Hstep.
Qed.

#[export] Instance noempty_instance : NoEmptyEdge G V E.
Proof.
  constructor.
  intros g [u v] Hg He.
  exists u, v. split; [reflexivity | exact He].
Qed.

#[export] Instance stepunique_instance : StepUniqueDirected G V E.
Proof.
  constructor.
  intros g e x1 y1 x2 y2 Hg [He1 _] [He2 _].
  rewrite He1 in He2; inversion He2; auto.
Qed.

#[export] Instance simple_instance : SimpleGraph G V E.
Proof.
  constructor.
  - intros g e1 e2 x y Hg [He1 _] [He2 _].
    rewrite He1, He2. reflexivity.
  - intros g e x Hg [_ [Hx [_ Hloop]]].
    destruct Hg as [_ Hirrefl].
    exact (Hirrefl x Hx Hloop).
Qed.

#[export] Instance finite_instance : FiniteGraph G V E.
Proof.
  refine {| listV := vertices |}.
  intros g Hg v Hv.
  unfold vertices, vertex_valid in *.
  apply In_Zrange. exact Hv.
Defined.

#[export] Instance vlist_bijective_instance : VListBijective G V E.
Proof.
  refine {| bijective_listV := vertices |}.
  - intros g Hg. unfold vertices. apply NoDup_Zrange.
  - intros g Hg v.
    unfold vertices, vertex_valid.
    rewrite <- In_Zrange. reflexivity.
Defined.

End ZSimpleGraph.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import GraphLib.reachable.reachable_basic.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Module DFSAdjacencyList.

Definition is_reachable
    (g : ZSimpleGraph.G) (source target : Z) : Prop :=
  @reachable ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g source target.

Fixpoint addressed_sll
    (cursor : addr) (node_addrs : list addr) (values : list Z)
    : Assertion :=
  match node_addrs, values with
  | nil, nil => “ cursor = NULL ” && emp
  | node :: node_addrs', datum :: values' =>
      “ cursor = node /\ node <> NULL ” &&
      EX next : addr,
        &(node # "list" ->ₛ "data") # Int |-> datum **
        &(node # "list" ->ₛ "next") # Ptr |-> next **
        addressed_sll next node_addrs' values'
  | _, _ => “ False ”
  end.

Definition row_block
    (entry : addr * (list addr * list Z)) : Assertion :=
  addressed_sll (fst entry) (fst (snd entry)) (snd (snd entry)).

Definition list_blocks
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) : Assertion :=
  iter_sepcon
    (map row_block (combine row_ptrs (combine node_addrs rows))).

Definition empty_visited (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

(** The head-pointer array and all linked lists it owns.  Both ghost lists
    are explicit here so a recursive proof can keep their order fixed while
    splitting out and later restoring one adjacency row. *)
Definition linked_lists_rep
    (adjacency : addr) (vertex_count : Z)
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z))
    : Assertion :=
  “ Zlength row_ptrs = vertex_count /\
    Zlength node_addrs = vertex_count /\
    Zlength rows = vertex_count ” &&
  PtrArray.full adjacency vertex_count row_ptrs **
  list_blocks row_ptrs node_addrs rows.

(** A convenience layer that fixes the row contents but hides the physical
    array of list-head pointers. *)
Definition linked_lists
    (adjacency : addr) (vertex_count : Z) (rows : list (list Z))
    : Assertion :=
  EX row_ptrs : list addr, EX node_addrs : list (list addr),
    linked_lists_rep adjacency vertex_count row_ptrs node_addrs rows.

(** The logical contents of every row exactly enumerate the outgoing
    neighbors in the concrete simple graph. *)
Definition adjacency_lists_model
    (g : ZSimpleGraph.G) (rows : list (list Z)) : Prop :=
  ZSimpleGraph.graph_wf g /\
  Zlength rows = ZSimpleGraph.vertex_count g /\
  Forall (fun row => NoDup row) rows /\
  forall u v,
    ZSimpleGraph.vertex_valid g u ->
    (In v (Znth u rows nil) <-> ZSimpleGraph.graph_step g u v).

(** Representation exposed to the recursive C proof.  [row_ptrs] and [rows]
    are immutable witnesses and therefore remain identical in the pre- and
    postcondition of every recursive call. *)
Definition store_graph
    (adjacency : addr) (g : ZSimpleGraph.G)
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) : Assertion :=
  “ adjacency_lists_model g rows ” &&
  linked_lists_rep
    adjacency (ZSimpleGraph.vertex_count g) row_ptrs node_addrs rows.

(** Intermediate abstraction for clients that need the fixed row order but
    do not need to name the concrete list-head pointers. *)
Definition graph_with_rows
    (adjacency : addr) (g : ZSimpleGraph.G) (rows : list (list Z))
    : Assertion :=
  EX row_ptrs : list addr, EX node_addrs : list (list addr),
    store_graph adjacency g row_ptrs node_addrs rows.

(** Public graph predicate: the storage order is irrelevant to clients. *)
Definition graph (adjacency : addr) (g : ZSimpleGraph.G) : Assertion :=
  EX rows : list (list Z),
    graph_with_rows adjacency g rows.

Definition visited
    (visited_ptr : addr) (g : ZSimpleGraph.G) (visited_set : Z -> Prop)
    : Assertion :=
  EX values : list Z,
    “ ZSimpleGraph.visited_values g values visited_set ” &&
    IntArray.full visited_ptr (ZSimpleGraph.vertex_count g) values.

End DFSAdjacencyList.
