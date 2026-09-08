Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import SetsClass.SetsClass.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.
From GraphLib Require Import graph_basic reachable_basic.
Require Export PVbench.Algorithms.kosaraju.rocq.kosaraju_refinement_lib.
From PVbench.Algorithms.kosaraju.rocq.groundtruth Require Import Kosaraju.

Import ListNotations.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Module Model := PVbench.Algorithms.kosaraju.rocq.kosaraju_model_lib.
Module Refinement := PVbench.Algorithms.kosaraju.rocq.kosaraju_refinement_lib.

Section CRefinement.

Context {G V E : Type}
        `{KG : KosarajuGraph G V E}
        (g : G)
        (g_valid : gvalid g).

Local Notation St := (@Model.St V).
Local Notation timer := (@Model.timer V).
Local Notation finish := (@Model.finish V).
Local Notation visited2 := (@Model.visited2 V).
Local Notation scc_id := (@Model.scc_id V).
Local Notation CFinishSequence := (@Refinement.CFinishSequence V).
Local Notation CPhase1Refinement :=
  (@Refinement.CPhase1Refinement G V E KG g).
Local Notation c_phase2_root_at := (@Refinement.c_phase2_root_at V).
Local Notation c_phase2_root_at_list := (@Refinement.c_phase2_root_at_list V).
Local Notation c_phase2_iteration :=
  (@Refinement.c_phase2_iteration G V E KG g).
Local Notation c_phase2_schedule :=
  (@Refinement.c_phase2_schedule G V E KG g).
Local Notation CLabelsRepresent := (@Refinement.CLabelsRepresent V).
Local Notation CLabelsCorrect :=
  (@Refinement.CLabelsCorrect G V E KG g).
Local Notation CRootLabelComponent := (@Refinement.CRootLabelComponent V).

Lemma c_finish_sequence_length : forall s fin,
  CFinishSequence s fin -> length fin = timer s.
Proof. intros s fin [H _]. exact H. Qed.

Lemma c_finish_sequence_lookup : forall s fin i v,
  CFinishSequence s fin ->
  (nth_error fin i = Some v <-> finish s v = S i).
Proof. intros s fin i v [_ H]. apply H. Qed.

Lemma c_finish_sequence_finished : forall s fin v,
  CFinishSequence s fin -> finish s v <> 0 ->
  exists i, nth_error fin i = Some v.
Proof.
  intros s fin v Hfin Hdone.
  destruct (finish s v) as [| i] eqn:Htime; [contradiction|].
  exists i. apply (proj2 (c_finish_sequence_lookup s fin i v Hfin)).
  exact Htime.
Qed.

Lemma c_phase2_root_at_list_in_range : forall fallback fin i,
  (i < length fin)%nat ->
  c_phase2_root_at_list fallback fin i = nth (length fin - S i) fin fallback.
Proof. reflexivity. Qed.

Lemma c_phase2_iteration_unfold : forall root,
  c_phase2_iteration root =
  if_else (fun st => visited2 st root)
    (ret tt)
    (visit2 root;; set_scc_id root root;; DFS_scc g root root).
Proof. reflexivity. Qed.

Lemma c_phase2_iteration_is_monadic_schedule_branch : forall root,
  c_phase2_iteration root =
  if_else (fun st => visited2 st root)
    (ret tt)
    (visit2 root;; set_scc_id root root;; DFS_scc g root root).
Proof. reflexivity. Qed.

Lemma c_phase2_schedule_done : forall fin_at n start,
  c_phase2_schedule fin_at n start 0 = ret tt.
Proof. intros. unfold c_phase2_schedule. apply kosaraju_scc_schedule_done. Qed.

Lemma c_labels_correct_of_R : forall s label,
  R g s ->
  (forall v, visited2 s v) ->
  CLabelsRepresent label s ->
  CLabelsCorrect label.
Proof.
  intros s label HR Hall Hrep u v.
  rewrite (Hrep u v).
  apply R_all_visited_correct with (st := s); assumption.
Qed.

Lemma c_labels_correct_of_monadic_post : forall s label,
  (forall v, visited2 s v) ->
  (forall u v, scc_id s u = scc_id s v <-> mutually_reachable g u v) ->
  CLabelsRepresent label s ->
  CLabelsCorrect label.
Proof.
  intros s label Hall Hmonad Hrep u v.
  rewrite (Hrep u v). apply Hmonad.
Qed.

Lemma c_root_label_component_eq : forall before after root label v,
  CRootLabelComponent before after root label ->
  ~ visited2 before v ->
  (label v = root <-> scc_id after v = scc_id after root).
Proof. intros before after root label v [_ H] Hnew. apply H; exact Hnew. Qed.

End CRefinement.
