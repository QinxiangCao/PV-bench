Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import PVbench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors.rocq.groundtruth.P010_48A_rock_paper_scissors_goal.
Require Import PVbench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors.rocq.groundtruth.P010_48A_rock_paper_scissors_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import PVbench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors.rocq.groundtruth.proof_lib.
Local Open Scope sac.

Ltac normalize_game_chars :=
  repeat match goal with
  | H : context [Array2.mixed_val
      (Znth ?j (Array2.replace_mixed_row ?i ?row ?rows) ?d) 0]
      |- _ =>
      rewrite (mixed_val_after_other_row_write rows d i j row)
        in H by (assumption || lia)
  end;
  repeat match goal with
  | Hcell : Znth 0 (Znth ?i ?rows nil) None =
        Some (Znth 0 (Znth ?i ?values nil) 0),
    H : context [Array2.mixed_val (Znth ?i ?rows ?d) 0] |- _ =>
      rewrite (mixed_val_of_initialized_cell rows values d i)
        in H by (assumption || lia)
  end.

Lemma proof_of_beats_entail_wit_2_split_goal_1 : beats_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH15 ia_pre ltac:(lia)).
  destruct PreH15 as [[[[Hlen_pos Hlen_lt] Hgame_len] Hcols] Hterminal].
  apply Hcols.
  lia.
Qed.

Lemma proof_of_beats_entail_wit_2 : beats_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_beats_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_beats_entail_wit_4_split_goal_1 : beats_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH18 ib_pre ltac:(lia)).
  destruct PreH18 as [[[[Hlen_pos Hlen_lt] Hgame_len] Hcols] Hterminal].
  apply Hcols.
  lia.
Qed.

Lemma proof_of_beats_entail_wit_4 : beats_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_beats_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_beats_return_wit_1_split_goal_1 : beats_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  normalize_game_chars.
  unfold Pre in PreH20.
  destruct PreH20 as [HG0 [HG1 HG2]].
  assert (Hia : ia_pre = 0 \/ ia_pre = 1 \/ ia_pre = 2) by lia.
  assert (Hib : ib_pre = 0 \/ ib_pre = 1 \/ ib_pre = 2) by lia.
  assert (HiaG : Gesture (Znth ia_pre players nil)).
  { destruct Hia as [-> | [-> | ->]]; assumption. }
  assert (HibG : Gesture (Znth ib_pre players nil)).
  { destruct Hib as [-> | [-> | ->]]; assumption. }
  unfold Gesture in HiaG, HibG.
  destruct HiaG as [HiaEq | [HiaEq | HiaEq]];
    destruct HibG as [HibEq | [HibEq | HibEq]];
    rewrite HiaEq in PreH2; rewrite HibEq in PreH1;
    cbn [rock paper scissors Znth] in PreH1, PreH2;
    try discriminate.
  all: unfold Beats; entailer!.
Qed.

Lemma proof_of_beats_return_wit_1_split_goal_spatial : beats_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (restore_two_mixed_cell_writes game_mem
    __default__List__App_option_Z ia_pre ib_pre
    (Znth 0 (Znth ia_pre players nil) 0)
    (Znth 0 (Znth ib_pre players nil) 0)) by (assumption || lia).
  cancel.
Qed.

Lemma proof_of_beats_return_wit_1 : beats_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_beats_return_wit_2_split_goal_1 : beats_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  normalize_game_chars.
  unfold Pre in PreH19.
  destruct PreH19 as [HG0 [HG1 HG2]].
  assert (Hia : ia_pre = 0 \/ ia_pre = 1 \/ ia_pre = 2) by lia.
  assert (Hib : ib_pre = 0 \/ ib_pre = 1 \/ ib_pre = 2) by lia.
  assert (HiaG : Gesture (Znth ia_pre players nil)).
  { destruct Hia as [-> | [-> | ->]]; assumption. }
  assert (HibG : Gesture (Znth ib_pre players nil)).
  { destruct Hib as [-> | [-> | ->]]; assumption. }
  unfold Gesture in HiaG, HibG.
  destruct HiaG as [HiaEq | [HiaEq | HiaEq]];
    destruct HibG as [HibEq | [HibEq | HibEq]];
    rewrite HiaEq in PreH2; rewrite HibEq in PreH1;
    cbn [rock paper scissors Znth] in PreH1, PreH2;
    try discriminate.
  all: unfold Beats; entailer!.
Qed.

Lemma proof_of_beats_return_wit_2_split_goal_spatial : beats_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (restore_two_mixed_cell_writes game_mem
    __default__List__App_option_Z ia_pre ib_pre
    (Znth 0 (Znth ia_pre players nil) 0)
    (Znth 0 (Znth ib_pre players nil) 0)) by (assumption || lia).
  cancel.
Qed.

Lemma proof_of_beats_return_wit_2 : beats_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_beats_return_wit_3_split_goal_1 : beats_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  normalize_game_chars.
  unfold Pre in PreH21.
  destruct PreH21 as [HG0 [HG1 HG2]].
  assert (Hia_idx : ia_pre = 0 \/ ia_pre = 1 \/ ia_pre = 2) by lia.
  assert (Hib_idx : ib_pre = 0 \/ ib_pre = 1 \/ ib_pre = 2) by lia.
  assert (Hia : Gesture (Znth ia_pre players nil)).
  { destruct Hia_idx as [-> | [-> | ->]]; assumption. }
  assert (Hib : Gesture (Znth ib_pre players nil)).
  { destruct Hib_idx as [-> | [-> | ->]]; assumption. }
  unfold Gesture in Hia, Hib.
  destruct Hia as [HiaEq | [HiaEq | HiaEq]];
    destruct Hib as [HibEq | [HibEq | HibEq]];
    rewrite HiaEq in PreH2; rewrite HibEq in PreH1;
    cbn [rock paper scissors Znth] in PreH1, PreH2;
    try discriminate.
  all: unfold Beats; entailer!.
  all: unfold rock, paper, scissors in *; simpl in *; intuition congruence.
Qed.

Lemma proof_of_beats_return_wit_3_split_goal_spatial : beats_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (restore_two_mixed_cell_writes game_mem
    __default__List__App_option_Z ia_pre ib_pre
    (Znth 0 (Znth ia_pre players nil) 0)
    (Znth 0 (Znth ib_pre players nil) 0)) by (assumption || lia).
  cancel.
Qed.

Lemma proof_of_beats_return_wit_3 : beats_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_beats_return_wit_4_split_goal_1 : beats_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  normalize_game_chars.
  unfold Pre in PreH21.
  destruct PreH21 as [HG0 [HG1 HG2]].
  assert (Hia : ia_pre = 0 \/ ia_pre = 1 \/ ia_pre = 2) by lia.
  assert (Hib : ib_pre = 0 \/ ib_pre = 1 \/ ib_pre = 2) by lia.
  assert (HiaG : Gesture (Znth ia_pre players nil)).
  { destruct Hia as [-> | [-> | ->]]; assumption. }
  assert (HibG : Gesture (Znth ib_pre players nil)).
  { destruct Hib as [-> | [-> | ->]]; assumption. }
  unfold Gesture in HiaG, HibG.
  destruct HiaG as [HiaEq | [HiaEq | HiaEq]];
    destruct HibG as [HibEq | [HibEq | HibEq]];
    rewrite HiaEq in PreH2; rewrite HibEq in PreH1;
    cbn [rock paper scissors Znth] in PreH1, PreH2;
    try discriminate.
  all: unfold Beats; entailer!.
Qed.

Lemma proof_of_beats_return_wit_4_split_goal_spatial : beats_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (restore_two_mixed_cell_writes game_mem
    __default__List__App_option_Z ia_pre ib_pre
    (Znth 0 (Znth ia_pre players nil) 0)
    (Znth 0 (Znth ib_pre players nil) 0)) by (assumption || lia).
  cancel.
Qed.

Lemma proof_of_beats_return_wit_4 : beats_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_beats_return_wit_5_split_goal_1 : beats_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  normalize_game_chars.
  unfold Pre in PreH20.
  destruct PreH20 as [HG0 [HG1 HG2]].
  assert (Hia : Gesture (Znth ia_pre players nil)).
  {
    assert (ia_pre = 0 \/ ia_pre = 1 \/ ia_pre = 2) as Hidx by lia.
    destruct Hidx as [-> | [-> | ->]]; assumption.
  }
  unfold Gesture in Hia.
  destruct Hia as [Hia | [Hia | Hia]].
  - rewrite Hia in PreH3. unfold rock in PreH3. cbn in PreH3. lia.
  - rewrite Hia in PreH1. unfold paper in PreH1. cbn in PreH1. lia.
  - rewrite Hia in PreH2. unfold scissors in PreH2. cbn in PreH2. lia.
Qed.

Lemma proof_of_beats_return_wit_5_split_goal_spatial : beats_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (restore_two_mixed_cell_writes game_mem
    __default__List__App_option_Z ia_pre ib_pre
    (Znth 0 (Znth ia_pre players nil) 0)
    (Znth 0 (Znth ib_pre players nil) 0)) by (assumption || lia).
  cancel.
Qed.

Lemma proof_of_beats_return_wit_5 : beats_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_beats_return_wit_6_split_goal_1 : beats_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  normalize_game_chars.
  unfold Pre in PreH21.
  destruct PreH21 as [HG0 [HG1 HG2]].
  assert (Hia : Gesture (Znth ia_pre players nil)).
  {
    assert (ia_pre = 0 \/ ia_pre = 1 \/ ia_pre = 2) as Hidx by lia.
    destruct Hidx as [-> | [-> | ->]]; assumption.
  }
  assert (Hib : Gesture (Znth ib_pre players nil)).
  {
    assert (ib_pre = 0 \/ ib_pre = 1 \/ ib_pre = 2) as Hidx by lia.
    destruct Hidx as [-> | [-> | ->]]; assumption.
  }
  unfold Gesture in Hia, Hib.
  destruct Hia as [HiaEq | [HiaEq | HiaEq]];
    destruct Hib as [HibEq | [HibEq | HibEq]].
  all: rewrite HiaEq in PreH1, PreH2, PreH4;
    rewrite HibEq in PreH3;
    cbn [rock paper scissors Znth] in PreH1, PreH2, PreH3, PreH4;
    try discriminate.
  all: unfold Beats; entailer!;
    rewrite HiaEq, HibEq;
    unfold rock, paper, scissors; simpl; intuition congruence.
Qed.

Lemma proof_of_beats_return_wit_6_split_goal_spatial : beats_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (restore_two_mixed_cell_writes game_mem
    __default__List__App_option_Z ia_pre ib_pre
    (Znth 0 (Znth ia_pre players nil) 0)
    (Znth 0 (Znth ib_pre players nil) 0)) by (assumption || lia).
  cancel.
Qed.

Lemma proof_of_beats_return_wit_6 : beats_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_beats_return_wit_7_split_goal_1 : beats_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  normalize_game_chars.
  unfold Pre in PreH21.
  destruct PreH21 as [HG0 [HG1 HG2]].
  assert (Hia : Gesture (Znth ia_pre players nil)).
  {
    assert (ia_pre = 0 \/ ia_pre = 1 \/ ia_pre = 2) as Hidx by lia.
    destruct Hidx as [-> | [-> | ->]]; assumption.
  }
  assert (Hib : Gesture (Znth ib_pre players nil)).
  {
    assert (ib_pre = 0 \/ ib_pre = 1 \/ ib_pre = 2) as Hidx by lia.
    destruct Hidx as [-> | [-> | ->]]; assumption.
  }
  unfold Gesture in Hia, Hib.
  destruct Hia as [HiaEq | [HiaEq | HiaEq]];
    destruct Hib as [HibEq | [HibEq | HibEq]].
  all: rewrite HiaEq in PreH3;
    rewrite HibEq in PreH2;
    cbn [rock paper scissors Znth] in PreH2, PreH3;
    try discriminate.
  all: unfold Beats; entailer!;
    rewrite HiaEq, HibEq;
    unfold rock, paper, scissors; simpl; intuition congruence.
Qed.

Lemma proof_of_beats_return_wit_7_split_goal_spatial : beats_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (restore_two_mixed_cell_writes game_mem
    __default__List__App_option_Z ia_pre ib_pre
    (Znth 0 (Znth ia_pre players nil) 0)
    (Znth 0 (Znth ib_pre players nil) 0)) by (assumption || lia).
  cancel.
Qed.

Lemma proof_of_beats_return_wit_7 : beats_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_beats_partial_solve_wit_1_pure_split_goal_1 :
  beats_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (Znth_indep game_mem ia_pre __default__List__App_option_Z nil)
    by lia.
  unfold Array2.mixed_def.
  dump_pre_spatial.
  exists (Znth 0 (Znth ia_pre players nil) 0).
  exact PreH1.
Qed.

Lemma proof_of_beats_partial_solve_wit_1_pure : beats_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_beats_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_beats_partial_solve_wit_2_pure_split_goal_1 :
  beats_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  rewrite Znth_replace_Znth_Diff by lia.
  rewrite (Znth_indep game_mem ib_pre __default__List__App_option_Z nil)
    by lia.
  unfold Array2.mixed_def.
  dump_pre_spatial.
  exists (Znth 0 (Znth ib_pre players nil) 0).
  exact PreH1.
Qed.

Lemma proof_of_beats_partial_solve_wit_2_pure : beats_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_beats_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (63 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      assert (H0 := PreH8 0 ltac:(lia)).
      assert (H1 := PreH8 1 ltac:(lia)).
      assert (H2 := PreH8 2 ltac:(lia)).
      cbn in H0, H1, H2.
      unfold Spec.
      right; right; right.
      split; [reflexivity |].
      split; [exact H0 |].
      split.
      * intros [H10 H12].
        apply H1.
        split; assumption.
      * exact H2.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i.
  pose proof (PreH5 PreH2) as H2.
  pose proof (PreH10 PreH7) as H1.
  cbn in H1, H2.
  Exists (70 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      unfold Spec.
      left.
      split; [reflexivity |].
      split; [exact H1 | exact H2].
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i.
  pose proof (PreH6 PreH3) as H2.
  pose proof (PreH11 PreH8) as H1.
  cbn in H1, H2.
  Exists (77 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      unfold Spec.
      right; left.
      split; [reflexivity |].
      split; [exact H2 | exact H1].
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = 2) by lia.
  subst i.
  pose proof (PreH6 PreH3) as H2.
  pose proof (PreH11 PreH8) as H1.
  cbn in H1, H2.
  Exists (83 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      unfold Spec.
      right; right; left.
      split; [reflexivity |].
      split; [exact H1 | exact H2].
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    assert (i = 0 \/ i = 1 \/ i = 2) by lia;
    destruct H as [-> | [-> | ->]]; cbn; lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_2 : solver_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (i + 1) 3 ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_3 : solver_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    assert (i = 0 \/ i = 1 \/ i = 2) by lia;
    destruct H as [-> | [-> | ->]]; cbn; lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_4 : solver_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros row Hrow.
  specialize (PreH9 row Hrow) as Hinv.
  destruct PreH7 as [HG0 [HG1 HG2]].
  assert (Hpos : 0 < Zlength (Znth row players nil)).
  {
    assert (row = 0 \/ row = 1 \/ row = 2) by lia.
    destruct H as [-> | [-> | ->]].
    - unfold Gesture, rock, paper, scissors in HG0.
      destruct HG0 as [HG0 | [HG0 | HG0]]; rewrite HG0; reflexivity.
    - unfold Gesture, rock, paper, scissors in HG1.
      destruct HG1 as [HG1 | [HG1 | HG1]]; rewrite HG1; reflexivity.
    - unfold Gesture, rock, paper, scissors in HG2.
      destruct HG2 as [HG2 | [HG2 | HG2]]; rewrite HG2; reflexivity.
  }
  destruct Hinv as [[[Hlen Hgame] Hcols] Hterm].
  repeat split; assumption.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (i + 2) 3 ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_2 : solver_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.rem_bound_pos (i + 2) 3 ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_3 : solver_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    assert (i = 0 \/ i = 1 \/ i = 2) by lia;
    destruct H as [-> | [-> | ->]]; cbn; lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_4 : solver_partial_solve_wit_2_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros row Hrow.
  specialize (PreH14 row Hrow) as Hinv.
  destruct PreH12 as [HG0 [HG1 HG2]].
  assert (Hpos : 0 < Zlength (Znth row players nil)).
  {
    assert (row = 0 \/ row = 1 \/ row = 2) by lia.
    destruct H as [-> | [-> | ->]].
    - unfold Gesture, rock, paper, scissors in HG0.
      destruct HG0 as [HG0 | [HG0 | HG0]]; rewrite HG0; reflexivity.
    - unfold Gesture, rock, paper, scissors in HG1.
      destruct HG1 as [HG1 | [HG1 | HG1]]; rewrite HG1; reflexivity.
    - unfold Gesture, rock, paper, scissors in HG2.
      destruct HG2 as [HG2 | [HG2 | HG2]]; rewrite HG2; reflexivity.
  }
  destruct Hinv as [[[Hlen Hgame] Hcols] Hterm].
  repeat split; assumption.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_4.
Qed.
