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
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.SL Require Import GraphLib.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Require Import GraphLib.reachable.reachable_basic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope sac.

Module DFSAdjacencyMatrixGraphLib.
  Include GraphLibSig
    Arch32 BigEndian
    naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules
    naive_C_Rules.
End DFSAdjacencyMatrixGraphLib.
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
Definition graph_reachable
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @reachable
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance
    g u v.

(** The loop left after the initial visit performed by [dfs_program]. *)
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

