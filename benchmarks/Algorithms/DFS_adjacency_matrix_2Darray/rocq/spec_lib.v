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
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import GraphLib.reachable.reachable_basic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope sac.

Module DFSAdjacencyMatrix2Darray.
Definition graph_reachable
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @reachable
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance
    g u v.

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

