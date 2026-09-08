Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Require Export PVbench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors.rocq.spec_lib.

Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.

Lemma mixed_val_of_initialized_cell :
  forall (rows : list (list (option Z))) (values : list (list Z))
         (default_row : list (option Z)) i,
    0 <= i < Zlength rows ->
    Znth 0 (Znth i rows nil) None =
      Some (Znth 0 (Znth i values nil) 0) ->
    Array2.mixed_val (Znth i rows default_row) 0 =
      Znth 0 (Znth i values nil) 0.
Proof.
  intros rows values default_row i Hi Hcell.
  rewrite (Znth_indep rows i default_row nil) by exact Hi.
  unfold Array2.mixed_val.
  rewrite Hcell.
  reflexivity.
Qed.

Lemma mixed_val_after_other_row_write :
  forall (rows : list (list (option Z))) default_row i j row,
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    i <> j ->
    Array2.mixed_val
      (Znth j (Array2.replace_mixed_row i row rows) default_row) 0 =
    Array2.mixed_val (Znth j rows default_row) 0.
Proof.
  intros rows default_row i j row Hi Hj Hne.
  unfold Array2.replace_mixed_row.
  rewrite Znth_replace_Znth_Diff by assumption.
  reflexivity.
Qed.

Lemma restore_mixed_cell_write :
  forall (rows : list (list (option Z))) default_row i value,
    0 <= i < Zlength rows ->
    Znth 0 (Znth i rows nil) None = Some value ->
    Array2.replace_mixed_row i
      (replace_Znth 0
        (Some (Array2.mixed_val (Znth i rows default_row) 0))
        (Znth i rows default_row)) rows = rows.
Proof.
  intros rows default_row i value Hi Hcell.
  rewrite (Znth_indep rows i default_row nil) by exact Hi.
  unfold Array2.mixed_val.
  rewrite Hcell.
  rewrite <- Hcell.
  rewrite replace_Znth_Znth.
  apply Array2.replace_mixed_row_Znth.
Qed.

Lemma restore_two_mixed_cell_writes :
  forall (rows : list (list (option Z))) default_row i j vi vj,
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    i <> j ->
    Znth 0 (Znth i rows nil) None = Some vi ->
    Znth 0 (Znth j rows nil) None = Some vj ->
    let rows_i :=
      Array2.replace_mixed_row i
        (replace_Znth 0
          (Some (Array2.mixed_val (Znth i rows default_row) 0))
          (Znth i rows default_row)) rows in
    Array2.replace_mixed_row j
      (replace_Znth 0
        (Some (Array2.mixed_val (Znth j rows_i default_row) 0))
        (Znth j rows_i default_row)) rows_i = rows.
Proof.
  intros rows default_row i j vi vj Hi Hj Hne Hcell_i Hcell_j.
  cbn zeta.
  set (rows_i :=
    Array2.replace_mixed_row i
      (replace_Znth 0
        (Some (Array2.mixed_val (Znth i rows default_row) 0))
        (Znth i rows default_row)) rows).
  assert (Hrows_i : rows_i = rows).
  { unfold rows_i. eapply restore_mixed_cell_write; eauto. }
  rewrite Hrows_i.
  eapply restore_mixed_cell_write; eauto.
Qed.
