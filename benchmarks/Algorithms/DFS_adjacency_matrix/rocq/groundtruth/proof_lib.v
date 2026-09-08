Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.SL Require Import GraphLib.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
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
Require Export PVbench.Algorithms.DFS_adjacency_matrix.rocq.spec_lib.
Require Export PVbench.Algorithms.DFS_adjacency_matrix.rocq.helper_lib.
Require Import Coq.micromega.Lia.
Import DFSAdjacencyMatrix.

Lemma ZSimpleGraph_step_iff : forall (g : ZSimpleGraph.G)
    (u v : ZSimpleGraph.V),
  @step ZSimpleGraph.G ZSimpleGraph.V ZSimpleGraph.E
    ZSimpleGraph.graph_instance g u v <-> ZSimpleGraph.graph_step g u v.
Proof.
  intros g u v. unfold step; split.
  - intros [[x y] [He Hstep]].
    inversion He; exact Hstep.
  - intros Hstep. exists (u, v). split; [reflexivity | exact Hstep].
Qed.

Lemma adjacency_matrix_model_as_matrix_model :
  forall g rows,
    adjacency_matrix_model g rows ->
    MatrixGraph.model g (matrix_layout g rows).
Proof.
  intros g rows Hmodel.
  exact Hmodel.
Qed.

Lemma adjacency_matrix_model_step :
  forall g rows u v,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    (Znth v (Znth u rows nil) 0 = 1 <->
     ZSimpleGraph.graph_step g u v).
Proof.
  intros g rows u v Hmodel Hu Hv.
  pose proof
    (adjacency_matrix_model_as_matrix_model g rows Hmodel)
    as Hmatrix.
  pose proof
    (MatrixGraph.model_step g (matrix_layout g rows) u v
      Hmatrix Hu Hv) as Hstep.
  unfold MatrixGraph.cell, matrix_layout in Hstep.
  simpl in Hstep.
  exact Hstep.
Qed.

Lemma adjacency_matrix_model_bit :
  forall g rows u v,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    (Znth v (Znth u rows nil) 0 = 0 \/
     Znth v (Znth u rows nil) 0 = 1).
Proof.
  intros g rows u v Hmodel Hu Hv.
  pose proof
    (adjacency_matrix_model_as_matrix_model g rows Hmodel)
    as Hmatrix.
  pose proof
    (MatrixGraph.model_bit_cell g (matrix_layout g rows) u v
      Hmatrix Hu Hv) as Hbit.
  unfold MatrixGraph.cell, matrix_layout in Hbit.
  simpl in Hbit.
  exact Hbit.
Qed.

Lemma adjacency_matrix_model_nonzero_step :
  forall g rows u v d,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    Znth v (Znth u rows d) 0 <> 0 ->
    ZSimpleGraph.graph_step g u v.
Proof.
  intros g rows u v d Hmodel Hu Hv Hnonzero.
  assert (Hrow:
    Znth u rows d = Znth u rows nil).
  { pose proof
      (MatrixGraph.model_shape g (matrix_layout g rows) Hmodel)
      as Hshape.
    unfold matrix_layout in Hshape.
    simpl in Hshape.
    destruct Hshape as [Hlen _].
    apply Znth_indep.
    rewrite Hlen.
    unfold ZSimpleGraph.vertex_valid in Hu.
    exact Hu. }
  rewrite Hrow in Hnonzero.
  pose proof
    (adjacency_matrix_model_bit g rows u v Hmodel Hu Hv)
    as [Hzero | Hone].
  - contradiction.
  - apply (proj1
      (adjacency_matrix_model_step g rows u v Hmodel Hu Hv)).
    exact Hone.
Qed.

Lemma adjacency_matrix_model_zero_not_step :
  forall g rows u v d,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    Znth v (Znth u rows d) 0 = 0 ->
    ~ ZSimpleGraph.graph_step g u v.
Proof.
  intros g rows u v d Hmodel Hu Hv Hzero Hedge.
  assert (Hrow:
    Znth u rows d = Znth u rows nil).
  { pose proof
      (MatrixGraph.model_shape g (matrix_layout g rows) Hmodel)
      as Hshape.
    unfold matrix_layout in Hshape.
    simpl in Hshape.
    destruct Hshape as [Hlen _].
    apply Znth_indep.
    rewrite Hlen.
    unfold ZSimpleGraph.vertex_valid in Hu.
    exact Hu. }
  rewrite Hrow in Hzero.
  apply (proj2
    (adjacency_matrix_model_step g rows u v Hmodel Hu Hv)) in Hedge.
  lia.
Qed.

Lemma visited_values_after_visit__dfs_core :
  forall g values before u,
    ZSimpleGraph.visited_values g values before ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.visited_values g (replace_Znth u 1 values)
      (fun v => before v \/ v = u).
Proof.
  intros g values before u Hvalues Hu.
  unfold ZSimpleGraph.visited_values in *.
  destruct Hvalues as [Hlen [Hvalid Hvalue]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros v [Hv | ->]; auto.
    + intros v Hv.
      specialize (Hvalue v Hv) as [H01 Hiff].
      destruct (Z.eq_dec v u) as [-> | Hne].
      * rewrite Znth_replace_Znth_Same by
            (unfold ZSimpleGraph.vertex_valid in *; lia).
        split; [auto |].
        split; [tauto | intros; right; reflexivity].
      * rewrite Znth_replace_Znth_Diff by
            (unfold ZSimpleGraph.vertex_valid in *; lia).
        split; [exact H01 |].
        split.
        -- intros [Hb | Heq]; [apply Hiff; exact Hb | contradiction].
        -- intros Hbit. left. apply Hiff. exact Hbit.
Qed.

Lemma matrix_split_merge__dfs_core :
  forall matrix n rows i j (d : list Z),
    0 <= i < n ->
    0 <= j < n ->
    ((matrix + (i * n + j) * sizeof (INT)) # Int
      |-> Znth j (Znth i rows d) 0) **
    IntArray.missing_i (matrix + i * n * sizeof (INT))
      j 0 n (Znth i rows d) **
    IntArray2.missing_i matrix i 0 n n rows
    |-- IntArray2.full matrix n n rows.
Proof.
  intros matrix n rows i j d Hi Hj.
  replace (matrix + (i * n + j) * sizeof (INT))
    with ((matrix + i * n * sizeof (INT)) + j * sizeof (INT)) by lia.
  prop_apply (IntArray.missing_i_Zlength
    (matrix + i * n * sizeof (INT)) j 0 n (Znth i rows d)).
  Intros. rename H into Hrowlen.
  prop_apply (IntArray2.missing_i_Zlength matrix i 0 n n rows).
  Intros. rename H into Hrowslen.
  sep_apply (IntArray.missing_i_merge_to_full
    (matrix + i * n * sizeof (INT)) j n
    (Znth j (Znth i rows d) 0) (Znth i rows d)); try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof (IntArray2.missing_i_merge_to_full
    matrix i n n rows (Znth i rows d)) as Hmerge_rows.
  change (IntArray2.ElemArray.full (IntArray2.row_addr matrix n i)
    n (Znth i rows d))
    with (IntArray.full (matrix + i * n * sizeof (INT))
      n (Znth i rows d)) in Hmerge_rows.
  sep_apply Hmerge_rows; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
