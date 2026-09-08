Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From PVbench.Algorithms.optimized_selection_sort.rocq.groundtruth Require Import optimized_selection_sort_goal.
From PVbench.Algorithms.optimized_selection_sort.rocq.groundtruth Require Import optimized_selection_sort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import PVbench.Algorithms.optimized_selection_sort.rocq.groundtruth.proof_lib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_optimized_selection_sort_entail_wit_1_split_goal_1 : optimized_selection_sort_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_1_split_goal_2 : optimized_selection_sort_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_1_split_goal_3 : optimized_selection_sort_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_1 : optimized_selection_sort_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_2_split_goal_1 : optimized_selection_sort_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct H as [Hiq Hqj].
  assert (q_2 = i_2) by lia.
  subst q_2.
  lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_2_split_goal_2 : optimized_selection_sort_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_2 : optimized_selection_sort_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_1 : optimized_selection_sort_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_cur : Zlength cur_2 = n_pre).
  { rewrite Zlength_replace_Znth in PreH1.
    rewrite Zlength_replace_Znth in PreH1.
    exact PreH1. }
  destruct H as [[[Hp0 Hpi] Hiq] Hqn].
  assert (Himin : i_2 < min_index) by lia.
  destruct (Z.eq_dec p i_2) as [Hpeq | Hpneq].
  - subst p.
    assert (Hleft :
      Znth i_2
        (replace_Znth min_index (Znth i_2 cur_2 0)
          (replace_Znth i_2 (Znth min_index cur_2 0) cur_2)) 0 =
      Znth min_index cur_2 0).
    { rewrite Znth_replace_Znth_Diff by
          (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity. }
    rewrite Hleft.
    destruct (Z.eq_dec q min_index) as [Hqeq | Hqneq].
    + subst q.
      rewrite Znth_replace_Znth_Same by
          (rewrite Zlength_replace_Znth; lia).
      apply PreH17.
      lia.
    + rewrite Znth_replace_Znth_Diff by
          (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      apply PreH17.
      lia.
  - assert (Hplt : p < i_2) by lia.
    assert (Hleft :
      Znth p
        (replace_Znth min_index (Znth i_2 cur_2 0)
          (replace_Znth i_2 (Znth min_index cur_2 0) cur_2)) 0 =
      Znth p cur_2 0).
    { rewrite Znth_replace_Znth_Diff by
          (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity. }
    rewrite Hleft.
    destruct (Z.eq_dec q min_index) as [Hqeq | Hqneq].
    + subst q.
      rewrite Znth_replace_Znth_Same by
          (rewrite Zlength_replace_Znth; lia).
      apply PreH16.
      lia.
    + rewrite Znth_replace_Znth_Diff by
          (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      apply PreH16.
      lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_2 : optimized_selection_sort_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_cur : Zlength cur_2 = n_pre).
  { rewrite Zlength_replace_Znth in PreH1.
    rewrite Zlength_replace_Znth in PreH1.
    exact PreH1. }
  assert (Himin : i_2 < min_index) by lia.
  apply increasing_sublist_intro; try lia.
  intros p q [Hp0 [Hpq Hqi]].
  destruct (Z.eq_dec q i_2) as [Hqeq | Hqneq].
  - subst q.
    destruct (Z.eq_dec p i_2) as [Hpeq | Hpneq].
    + subst p. lia.
    + assert (Hleft :
        Znth p
          (replace_Znth min_index (Znth i_2 cur_2 0)
            (replace_Znth i_2 (Znth min_index cur_2 0) cur_2)) 0 =
        Znth p cur_2 0).
      { rewrite Znth_replace_Znth_Diff by
            (try rewrite Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Diff by lia.
        reflexivity. }
      assert (Hright :
        Znth i_2
          (replace_Znth min_index (Znth i_2 cur_2 0)
            (replace_Znth i_2 (Znth min_index cur_2 0) cur_2)) 0 =
        Znth min_index cur_2 0).
      { rewrite Znth_replace_Znth_Diff by
            (try rewrite Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Same by lia.
        reflexivity. }
      rewrite Hleft, Hright.
      apply PreH16.
      lia.
  - assert (Hqlt : q < i_2) by lia.
    repeat rewrite Znth_replace_Znth_Diff by
      (try rewrite Zlength_replace_Znth; lia).
    eapply (increasing_sublist_elim cur_2 0 i_2 p q); eauto; lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_3 : optimized_selection_sort_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_cur : Zlength cur_2 = n_pre).
  { rewrite Zlength_replace_Znth in PreH1.
    rewrite Zlength_replace_Znth in PreH1.
    exact PreH1. }
  eapply Permutation_trans.
  - exact PreH14.
  - apply permutation_swap_Znth_lt.
    lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1 : optimized_selection_sort_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_1 : optimized_selection_sort_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst min_index.
  assert (Hj : j = n_pre) by lia.
  destruct H as [[[Hp0 Hpi] Hiq] Hqn].
  destruct (Z_lt_ge_dec p i_2) as [Hplt | Hpge].
  - apply PreH15.
    lia.
  - assert (p = i_2) by lia.
    subst p.
    apply PreH16.
    lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_2 : optimized_selection_sort_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst min_index.
  apply increasing_sublist_intro; try lia.
  intros p q [Hp0 [Hpq Hqi]].
  destruct (Z.eq_dec q i_2) as [Hqeq | Hqneq].
  - subst q.
    destruct (Z.eq_dec p i_2) as [Hpeq | Hpneq].
    + subst p. lia.
    + apply PreH15. lia.
  - eapply (increasing_sublist_elim cur_2 0 i_2 p q); eauto; lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_2 : optimized_selection_sort_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_2.
Qed.

Lemma proof_of_optimized_selection_sort_return_wit_1_split_goal_1 : optimized_selection_sort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace cur with (sublist 0 n_pre cur).
  - apply increasing_sublist_intro; try lia.
    intros p q [Hp0 [Hpq Hqn]].
    destruct (Z_lt_ge_dec q i) as [Hqlt | Hqge].
    + eapply (increasing_sublist_elim cur 0 i p q); eauto; lia.
    + destruct (Z_lt_ge_dec p i) as [Hplt | Hpge].
      * apply PreH11. lia.
      * assert (p = q) by lia.
        subst q.
        lia.
  - rewrite sublist_self by lia.
    reflexivity.
Qed.

Lemma proof_of_optimized_selection_sort_return_wit_1_split_goal_2 : optimized_selection_sort_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold optimized_selection_sort_result.
  split.
  - exact PreH9.
  - eapply proof_of_optimized_selection_sort_return_wit_1_split_goal_1; eauto.
Qed.

Lemma proof_of_optimized_selection_sort_return_wit_1 : optimized_selection_sort_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_optimized_selection_sort_return_wit_1_split_goal_1.
  - Goal_apply proof_of_optimized_selection_sort_return_wit_1_split_goal_2.
Qed.
