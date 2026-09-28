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
Require Import PVbench.Codeforces.examples_shard00.P025_1207B_square_filling.rocq.groundtruth.P025_1207B_square_filling_goal.
Require Import PVbench.Codeforces.examples_shard00.P025_1207B_square_filling.rocq.groundtruth.P025_1207B_square_filling_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import PVbench.Codeforces.examples_shard00.P025_1207B_square_filling.rocq.groundtruth.proof_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (@nil (Z * Z)).
  unfold repeat_Z.
  rewrite made_state_nil__initialization.
  rewrite staged_ops_nil__initialization.
  replace (Z.to_nat 2500) with (2500%nat) by reflexivity.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia;
      try apply ScanOperations_empty__initialization;
      rewrite Zlength_correct, repeat_length; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists result_2.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full (&( "made" )) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists result_2.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full (&( "made" )) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    apply (ScanOperations_row_advance__operation_scan_boundaries
             n_pre m_pre matrix i j result_2).
    + exact PreH20.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (M1 := Array2.replace_mixed_row i
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth i matrix_mem __default__List__App_option_Z) j))
      (Znth i matrix_mem __default__List__App_option_Z)) matrix_mem) in *.
  set (M2 := Array2.replace_mixed_row (i + 1)
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth (i + 1) M1 __default__List__App_option_Z) j))
      (Znth (i + 1) M1 __default__List__App_option_Z)) M1) in *.
  set (M3 := Array2.replace_mixed_row i
    (replace_Znth (j + 1)
      (Some (Array2.mixed_val
        (Znth i M2 __default__List__App_option_Z) (j + 1)))
      (Znth i M2 __default__List__App_option_Z)) M2) in *.
  set (M4 := Array2.replace_mixed_row (i + 1)
    (replace_Znth (j + 1)
      (Some (Array2.mixed_val
        (Znth (i + 1) M3 __default__List__App_option_Z) (j + 1)))
      (Znth (i + 1) M3 __default__List__App_option_Z)) M3) in *.
  assert (Hdef_i_j :
    Array2.mixed_def
      (Znth i matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth i matrix nil) 0).
    rewrite (Znth_indep matrix_mem i
      __default__List__App_option_Z nil) by lia.
    apply PreH35; lia. }
  assert (HM1 : M1 = matrix_mem).
  { unfold M1. rewrite <- (Array2.mixed_def_val _ _ Hdef_i_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_ip1_j :
    Array2.mixed_def
      (Znth (i + 1) matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth (i + 1) matrix nil) 0).
    rewrite (Znth_indep matrix_mem (i + 1)
      __default__List__App_option_Z nil) by lia.
    apply PreH35; lia. }
  assert (HM2 : M2 = matrix_mem).
  { unfold M2. rewrite HM1.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_ip1_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_i_jp1 :
    Array2.mixed_def
      (Znth i matrix_mem __default__List__App_option_Z) (j + 1)).
  { unfold Array2.mixed_def.
    exists (Znth (j + 1) (Znth i matrix nil) 0).
    rewrite (Znth_indep matrix_mem i
      __default__List__App_option_Z nil) by lia.
    apply PreH35; lia. }
  assert (HM3 : M3 = matrix_mem).
  { unfold M3. rewrite HM2.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_i_jp1).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_ip1_jp1 :
    Array2.mixed_def
      (Znth (i + 1) matrix_mem __default__List__App_option_Z) (j + 1)).
  { unfold Array2.mixed_def.
    exists (Znth (j + 1) (Znth (i + 1) matrix nil) 0).
    rewrite (Znth_indep matrix_mem (i + 1)
      __default__List__App_option_Z nil) by lia.
    apply PreH35; lia. }
  assert (HM4 : M4 = matrix_mem).
  { unfold M4. rewrite HM3.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_ip1_jp1).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite HM3 in PreH21.
  rewrite HM2 in PreH22.
  rewrite HM1 in PreH23.
  assert (Hval : forall row col,
    0 <= row < n_pre -> 0 <= col < m_pre ->
    Array2.mixed_val
      (Znth row matrix_mem __default__List__App_option_Z) col =
    Znth col (Znth row matrix nil) 0).
  { intros row col Hr Hc. unfold Array2.mixed_val.
    rewrite (Znth_indep matrix_mem row
      __default__List__App_option_Z nil) by lia.
    rewrite (PreH35 row Hr col Hc). reflexivity. }
  rewrite (Hval (i + 1) (j + 1) ltac:(lia) ltac:(lia)) in PreH21.
  rewrite (Hval i (j + 1) ltac:(lia) ltac:(lia)) in PreH22.
  rewrite (Hval (i + 1) j ltac:(lia) ltac:(lia)) in PreH23.
  rewrite (Hval i j ltac:(lia) ltac:(lia)) in PreH24.
  assert (Hone1 : Znth j (Znth i matrix nil) 0 = 1).
  { destruct (PreH32 i j ltac:(lia)) as [Hz | Ho]; [lia|exact Ho]. }
  assert (Hone2 : Znth j (Znth (i + 1) matrix nil) 0 = 1).
  { destruct (PreH32 (i + 1) j ltac:(lia)) as [Hz | Ho]; [lia|exact Ho]. }
  assert (Hone3 : Znth (j + 1) (Znth i matrix nil) 0 = 1).
  { destruct (PreH32 i (j + 1) ltac:(lia)) as [Hz | Ho]; [lia|exact Ho]. }
  assert (Hone4 : Znth (j + 1) (Znth (i + 1) matrix nil) 0 = 1).
  { destruct (PreH32 (i + 1) (j + 1) ltac:(lia)) as [Hz | Ho]; [lia|exact Ho]. }
  assert (Hall : SquareAllOn matrix i j).
  { unfold SquareAllOn. auto. }
  assert (Hscan : ScanOperations n_pre m_pre matrix i (j + 1)
    (result_2 ++ cons (i, j) nil)).
  { eapply ScanOperations_add_square__square_decision_transition; eauto; lia. }
  assert (Hmade :
    replace_Znth ((i + 1) * 50 + (j + 1)) 1
      (replace_Znth (i * 50 + (j + 1)) 1
        (replace_Znth ((i + 1) * 50 + j) 1
          (replace_Znth (i * 50 + j) 1 (made_state result_2)))) =
    made_state (result_2 ++ cons (i, j) nil)).
  { apply made_state_snoc__square_decision_transition; lia. }
  assert (Hstaged :
    replace_Znth (2 * count + 1) (Some (j + 1))
      (replace_Znth (2 * count) (Some (i + 1))
        (staged_ops result_2)) =
    staged_ops (result_2 ++ cons (i, j) nil)).
  { apply staged_ops_snoc__square_decision_transition; assumption. }
  assert (Hcount : count + 1 = Zlength (result_2 ++ cons (i, j) nil)).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hmade_len : Zlength (made_state (result_2 ++ cons (i, j) nil)) = 2500).
  { rewrite <- Hmade. repeat rewrite Zlength_replace_Znth. exact PreH45. }
  assert (Hstaged_len : Zlength (staged_ops (result_2 ++ cons (i, j) nil)) = 5000).
  { rewrite <- Hstaged. repeat rewrite Zlength_replace_Znth. exact PreH46. }
  pose (List.app result_2 (cons (i, j) nil)) as result.
  Exists result.
  unfold result.
  rewrite HM4, Hmade, Hstaged.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full ( &( "made" ) ) 2500
      (made_state (result_2 ++ cons (i, j) nil))).
    cancel (IntArray.mixed_full ops_pre 5000
      (staged_ops (result_2 ++ cons (i, j) nil))).
  - split_pures; dump_pre_spatial; try assumption; nia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (M1 := Array2.replace_mixed_row i
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth i matrix_mem __default__List__App_option_Z) j))
      (Znth i matrix_mem __default__List__App_option_Z)) matrix_mem) in *.
  set (M2 := Array2.replace_mixed_row (i + 1)
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth (i + 1) M1 __default__List__App_option_Z) j))
      (Znth (i + 1) M1 __default__List__App_option_Z)) M1) in *.
  set (M3 := Array2.replace_mixed_row i
    (replace_Znth (j + 1)
      (Some (Array2.mixed_val
        (Znth i M2 __default__List__App_option_Z) (j + 1)))
      (Znth i M2 __default__List__App_option_Z)) M2) in *.
  assert (Hdef_i_j :
    Array2.mixed_def
      (Znth i matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth i matrix nil) 0).
    rewrite (Znth_indep matrix_mem i
      __default__List__App_option_Z nil) by lia.
    apply PreH14; lia. }
  assert (HM1 : M1 = matrix_mem).
  { unfold M1. rewrite <- (Array2.mixed_def_val _ _ Hdef_i_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_ip1_j :
    Array2.mixed_def
      (Znth (i + 1) matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth (i + 1) matrix nil) 0).
    rewrite (Znth_indep matrix_mem (i + 1)
      __default__List__App_option_Z nil) by lia.
    apply PreH14; lia. }
  assert (HM2 : M2 = matrix_mem).
  { unfold M2. rewrite HM1.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_ip1_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_i_jp1 :
    Array2.mixed_def
      (Znth i matrix_mem __default__List__App_option_Z) (j + 1)).
  { unfold Array2.mixed_def.
    exists (Znth (j + 1) (Znth i matrix nil) 0).
    rewrite (Znth_indep matrix_mem i
      __default__List__App_option_Z nil) by lia.
    apply PreH14; lia. }
  assert (HM3 : M3 = matrix_mem).
  { unfold M3. rewrite HM2.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_i_jp1).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hcell :
    Znth (j + 1) (Znth i matrix_mem nil) None =
    Some (Znth (j + 1) (Znth i matrix nil) 0)).
  { apply PreH14; lia. }
  assert (Hrow :
    Znth i matrix_mem __default__List__App_option_Z =
    Znth i matrix_mem nil).
  { apply Znth_indep. lia. }
  rewrite HM2 in PreH1.
  assert (Hzero : Znth (j + 1) (Znth i matrix nil) 0 = 0).
  { rewrite Hrow in PreH1.
    unfold Array2.mixed_val in PreH1. rewrite Hcell in PreH1. exact PreH1. }
  assert (Hnot : ~ SquareAllOn matrix i j).
  { unfold SquareAllOn. intros [_ [_ [H _]]]. congruence. }
  assert (Hscan : ScanOperations n_pre m_pre matrix i (j + 1) result_2).
  { eapply ScanOperations_skip_square__square_decision_transition; eauto; lia. }
  Exists result_2.
  rewrite HM3.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full ( &( "made" ) ) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcell :
    Znth j (Znth i matrix_mem nil) None =
    Some (Znth j (Znth i matrix nil) 0)).
  { apply PreH12; lia. }
  assert (Hrow :
    Znth i matrix_mem __default__List__App_option_Z =
    Znth i matrix_mem nil).
  { apply Znth_indep. lia. }
  assert (Hzero : Znth j (Znth i matrix nil) 0 = 0).
  { rewrite Hrow in PreH1.
    unfold Array2.mixed_val in PreH1. rewrite Hcell in PreH1. exact PreH1. }
  assert (Hnot : ~ SquareAllOn matrix i j).
  { unfold SquareAllOn. intros [H _]. congruence. }
  assert (Hscan : ScanOperations n_pre m_pre matrix i (j + 1) result_2).
  { eapply ScanOperations_skip_square__square_decision_transition; eauto; lia. }
  assert (Hrestore :
    Array2.replace_mixed_row i
      (replace_Znth j
        (Some (Array2.mixed_val
          (Znth i matrix_mem __default__List__App_option_Z) j))
        (Znth i matrix_mem __default__List__App_option_Z)) matrix_mem = matrix_mem).
  { rewrite Hrow. unfold Array2.mixed_val. rewrite Hcell. simpl.
    rewrite <- Hcell.
    apply Array2.replace_mixed_row_roundtrip. }
  Exists result_2.
  rewrite Hrestore.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full ( &( "made" ) ) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_4 : solver_entail_wit_6_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (M1 := Array2.replace_mixed_row i
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth i matrix_mem __default__List__App_option_Z) j))
      (Znth i matrix_mem __default__List__App_option_Z)) matrix_mem) in *.
  set (M2 := Array2.replace_mixed_row (i + 1)
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth (i + 1) M1 __default__List__App_option_Z) j))
      (Znth (i + 1) M1 __default__List__App_option_Z)) M1) in *.
  assert (Hdef_i_j :
    Array2.mixed_def
      (Znth i matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth i matrix nil) 0).
    rewrite (Znth_indep matrix_mem i
      __default__List__App_option_Z nil) by lia.
    apply PreH13; lia. }
  assert (HM1 : M1 = matrix_mem).
  { unfold M1. rewrite <- (Array2.mixed_def_val _ _ Hdef_i_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_ip1_j :
    Array2.mixed_def
      (Znth (i + 1) matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth (i + 1) matrix nil) 0).
    rewrite (Znth_indep matrix_mem (i + 1)
      __default__List__App_option_Z nil) by lia.
    apply PreH13; lia. }
  assert (HM2 : M2 = matrix_mem).
  { unfold M2. rewrite HM1.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_ip1_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hcell :
    Znth j (Znth (i + 1) matrix_mem nil) None =
    Some (Znth j (Znth (i + 1) matrix nil) 0)).
  { apply PreH13; lia. }
  assert (Hrow :
    Znth (i + 1) matrix_mem __default__List__App_option_Z =
    Znth (i + 1) matrix_mem nil).
  { apply Znth_indep. lia. }
  rewrite HM1 in PreH1.
  assert (Hzero : Znth j (Znth (i + 1) matrix nil) 0 = 0).
  { rewrite Hrow in PreH1.
    unfold Array2.mixed_val in PreH1. rewrite Hcell in PreH1. exact PreH1. }
  assert (Hnot : ~ SquareAllOn matrix i j).
  { unfold SquareAllOn. intros [_ [H _]]. congruence. }
  assert (Hscan : ScanOperations n_pre m_pre matrix i (j + 1) result_2).
  { eapply ScanOperations_skip_square__square_decision_transition; eauto; lia. }
  Exists result_2.
  rewrite HM2.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full ( &( "made" ) ) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_5 : solver_entail_wit_6_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (M1 := Array2.replace_mixed_row i
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth i matrix_mem __default__List__App_option_Z) j))
      (Znth i matrix_mem __default__List__App_option_Z)) matrix_mem) in *.
  set (M2 := Array2.replace_mixed_row (i + 1)
    (replace_Znth j
      (Some (Array2.mixed_val
        (Znth (i + 1) M1 __default__List__App_option_Z) j))
      (Znth (i + 1) M1 __default__List__App_option_Z)) M1) in *.
  set (M3 := Array2.replace_mixed_row i
    (replace_Znth (j + 1)
      (Some (Array2.mixed_val
        (Znth i M2 __default__List__App_option_Z) (j + 1)))
      (Znth i M2 __default__List__App_option_Z)) M2) in *.
  set (M4 := Array2.replace_mixed_row (i + 1)
    (replace_Znth (j + 1)
      (Some (Array2.mixed_val
        (Znth (i + 1) M3 __default__List__App_option_Z) (j + 1)))
      (Znth (i + 1) M3 __default__List__App_option_Z)) M3) in *.
  assert (Hdef_i_j :
    Array2.mixed_def
      (Znth i matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth i matrix nil) 0).
    rewrite (Znth_indep matrix_mem i
      __default__List__App_option_Z nil) by lia.
    apply PreH15; lia. }
  assert (HM1 : M1 = matrix_mem).
  { unfold M1. rewrite <- (Array2.mixed_def_val _ _ Hdef_i_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_ip1_j :
    Array2.mixed_def
      (Znth (i + 1) matrix_mem __default__List__App_option_Z) j).
  { unfold Array2.mixed_def.
    exists (Znth j (Znth (i + 1) matrix nil) 0).
    rewrite (Znth_indep matrix_mem (i + 1)
      __default__List__App_option_Z nil) by lia.
    apply PreH15; lia. }
  assert (HM2 : M2 = matrix_mem).
  { unfold M2. rewrite HM1.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_ip1_j).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_i_jp1 :
    Array2.mixed_def
      (Znth i matrix_mem __default__List__App_option_Z) (j + 1)).
  { unfold Array2.mixed_def.
    exists (Znth (j + 1) (Znth i matrix nil) 0).
    rewrite (Znth_indep matrix_mem i
      __default__List__App_option_Z nil) by lia.
    apply PreH15; lia. }
  assert (HM3 : M3 = matrix_mem).
  { unfold M3. rewrite HM2.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_i_jp1).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hdef_ip1_jp1 :
    Array2.mixed_def
      (Znth (i + 1) matrix_mem __default__List__App_option_Z) (j + 1)).
  { unfold Array2.mixed_def.
    exists (Znth (j + 1) (Znth (i + 1) matrix nil) 0).
    rewrite (Znth_indep matrix_mem (i + 1)
      __default__List__App_option_Z nil) by lia.
    apply PreH15; lia. }
  assert (HM4 : M4 = matrix_mem).
  { unfold M4. rewrite HM3.
    rewrite <- (Array2.mixed_def_val _ _ Hdef_ip1_jp1).
    apply Array2.replace_mixed_row_roundtrip. }
  assert (Hcell :
    Znth (j + 1) (Znth (i + 1) matrix_mem nil) None =
    Some (Znth (j + 1) (Znth (i + 1) matrix nil) 0)).
  { apply PreH15; lia. }
  assert (Hrow :
    Znth (i + 1) matrix_mem __default__List__App_option_Z =
    Znth (i + 1) matrix_mem nil).
  { apply Znth_indep. lia. }
  rewrite HM3 in PreH1.
  assert (Hzero : Znth (j + 1) (Znth (i + 1) matrix nil) 0 = 0).
  { rewrite Hrow in PreH1.
    unfold Array2.mixed_val in PreH1. rewrite Hcell in PreH1. exact PreH1. }
  assert (Hnot : ~ SquareAllOn matrix i j).
  { unfold SquareAllOn. intros [_ [_ [_ H]]]. congruence. }
  assert (Hscan : ScanOperations n_pre m_pre matrix i (j + 1) result_2).
  { eapply ScanOperations_skip_square__square_decision_transition; eauto; lia. }
  Exists result_2.
  rewrite HM4.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full ( &( "made" ) ) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre - 1) by lia.
  subst i.
  Exists result_2.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full (&( "made" )) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try apply CheckedPrefix_empty__validation_prefix_boundaries.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists result_2.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full (&( "made" )) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = m_pre) by lia.
  subst j.
  Exists result_2.
  split_pure_spatial.
  - cancel (IntArray2.mixed_full a_pre 50 50 matrix_mem).
    cancel (IntArray.full (&( "made" )) 2500 (made_state result_2)).
    cancel (IntArray.mixed_full ops_pre 5000 (staged_ops result_2)).
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try (eapply CheckedPrefix_row_advance__validation_prefix_boundaries;
           eauto).
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrowdefault :
    Znth i matrix_mem __default__List__App_option_Z =
    Znth i matrix_mem nil).
  { apply Znth_indep. lia. }
  pose proof (PreH12 i ltac:(lia) j ltac:(lia)) as Hmem.
  assert (Hmixed :
    Array2.mixed_val (Znth i matrix_mem __default__List__App_option_Z) j =
    Znth j (Znth i matrix nil) 0).
  { unfold Array2.mixed_val. rewrite Hrowdefault. rewrite Hmem. reflexivity. }
  pose proof (made_state_index__validation_failure_result result_2 i j
    ltac:(lia) ltac:(lia)) as [Hmade _].
  assert (Hcurrent :
    Znth j (Znth i matrix nil) 0 = 1 <-> CellCovered result_2 i j).
  { rewrite Hmixed in PreH1. rewrite PreH1. exact Hmade. }
  pose proof (CheckedPrefix_cell_advance__validation_failure_result
    n_pre m_pre matrix result_2 i j PreH22 ltac:(lia) ltac:(lia) Hcurrent)
    as Hnext.
  Exists result_2.
  split_pure_spatial.
  - rewrite Hmixed.
    rewrite Hrowdefault.
    rewrite <- Hmem.
    rewrite replace_Znth_Znth.
    rewrite Array2.replace_mixed_row_Znth.
    cancel.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i_2 = n_pre) by lia.
  subst i_2.
  Exists (staged_ops result_2) result_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold Spec.
      left.
      exists result_2.
      split; [reflexivity |].
      apply completed_scan_filling__successful_result.
      * lia.
      * exact PreH18.
      * exact PreH19.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      intros k Hk.
      apply staged_ops_pair_index__successful_result; lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrowdefault :
    Znth i_2 matrix_mem __default__List__App_option_Z =
    Znth i_2 matrix_mem nil).
  { apply Znth_indep. lia. }
  pose proof (PreH12 i_2 ltac:(lia) j ltac:(lia)) as Hmem.
  assert (Hmixed :
    Array2.mixed_val
      (Znth i_2 matrix_mem __default__List__App_option_Z) j =
    Znth j (Znth i_2 matrix nil) 0).
  { unfold Array2.mixed_val. rewrite Hrowdefault. rewrite Hmem. reflexivity. }
  rewrite Hmixed in PreH1.
  pose proof (PreH9 i_2 j ltac:(lia)) as Hbinary.
  pose proof (mismatch_implies_no_filling__validation_failure_result
    n_pre m_pre matrix result_2 i_2 j
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    Hbinary PreH21 PreH1) as Hnone.
  Right.
  Exists (staged_ops result_2).
  split_pure_spatial.
  - rewrite Hmixed.
    rewrite Hrowdefault.
    rewrite <- Hmem.
    rewrite replace_Znth_Znth.
    rewrite Array2.replace_mixed_row_Znth.
    cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold Spec. right. split; [reflexivity | exact Hnone].
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (IntArray2.mixed_full_split_to_mixed_missing_i
       a_pre i 50 50 matrix_mem ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.mixed_full_split_to_mixed_missing_i
       (IntArray2.row_addr a_pre 50 i) j 50
       (Znth i matrix_mem nil) None ltac:(lia)).
  unfold Array2.mixed_def.
  dump_pre_spatial.
  rewrite (Znth_indep matrix_mem i __default__List__App_option_Z nil) by lia.
  exists (Znth j (Znth i matrix nil) 0).
  apply PreH21; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_1 : solver_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | |- context [IntArray2.mixed_full a_pre 50 50 ?rows] =>
      sep_apply_l_atomic
        (IntArray2.mixed_full_split_to_mixed_missing_i
           a_pre (i + 1) 50 50 rows ltac:(lia))
  end.
  match goal with
  | |- context [IntArray2.ElemArray.mixed_full ?addr 50 ?row] =>
      sep_apply_l_atomic
        (IntArray.mixed_full_split_to_mixed_missing_i
           addr j 50 row None ltac:(lia))
  end.
  unfold Array2.mixed_def, Array2.replace_mixed_row.
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff
             __default__List__App_option_Z matrix_mem i (i + 1) _) by lia.
  rewrite (Znth_indep matrix_mem (i + 1)
             __default__List__App_option_Z nil) by lia.
  exists (Znth j (Znth (i + 1) matrix nil) 0).
  apply PreH22; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | |- context [IntArray2.mixed_full a_pre 50 50 ?rows] =>
      sep_apply_l_atomic
        (IntArray2.mixed_full_split_to_mixed_missing_i
           a_pre i 50 50 rows ltac:(lia))
  end.
  match goal with
  | |- context [IntArray2.ElemArray.mixed_full ?addr 50 ?row] =>
      sep_apply_l_atomic
        (IntArray.mixed_full_split_to_mixed_missing_i
           addr (j + 1) 50 row None ltac:(lia))
  end.
  unfold Array2.mixed_def, Array2.replace_mixed_row.
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff
             __default__List__App_option_Z _ (i + 1) i _) by
    (rewrite ?Zlength_replace_Znth__array_cell_extraction; lia).
  rewrite (Znth_replace_Znth_Same
             __default__List__App_option_Z matrix_mem i _) by lia.
  rewrite (Znth_indep matrix_mem i
             __default__List__App_option_Z nil) by lia.
  rewrite (Znth_replace_Znth_Diff None _ j (j + 1) _) by
    (rewrite ?Zlength_replace_Znth__array_cell_extraction;
     try rewrite PreH22 by lia; lia).
  exists (Znth (j + 1) (Znth i matrix nil) 0).
  apply PreH23; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure_split_goal_1 : solver_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | |- context [IntArray2.mixed_full a_pre 50 50 ?rows] =>
      sep_apply_l_atomic
        (IntArray2.mixed_full_split_to_mixed_missing_i
           a_pre (i + 1) 50 50 rows ltac:(lia))
  end.
  match goal with
  | |- context [IntArray2.ElemArray.mixed_full ?addr 50 ?row] =>
      sep_apply_l_atomic
        (IntArray.mixed_full_split_to_mixed_missing_i
           addr (j + 1) 50 row None ltac:(lia))
  end.
  unfold Array2.mixed_def, Array2.replace_mixed_row.
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff
             __default__List__App_option_Z _ i (i + 1) _) by
    (rewrite ?Zlength_replace_Znth__array_cell_extraction; lia).
  rewrite (Znth_replace_Znth_Same
             __default__List__App_option_Z _ (i + 1) _) by
    (rewrite ?Zlength_replace_Znth__array_cell_extraction; lia).
  rewrite (Znth_replace_Znth_Diff
             __default__List__App_option_Z matrix_mem i (i + 1) _) by lia.
  rewrite (Znth_indep matrix_mem (i + 1)
             __default__List__App_option_Z nil) by lia.
  rewrite (Znth_replace_Znth_Diff None _ j (j + 1) _) by
    (rewrite ?Zlength_replace_Znth__array_cell_extraction;
     try rewrite PreH23 by lia; lia).
  exists (Znth (j + 1) (Znth (i + 1) matrix nil) 0).
  apply PreH24; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure_split_goal_1 : solver_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (IntArray2.mixed_full_split_to_mixed_missing_i
       a_pre i 50 50 matrix_mem ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.mixed_full_split_to_mixed_missing_i
       (IntArray2.row_addr a_pre 50 i) j 50
       (Znth i matrix_mem nil) None ltac:(lia)).
  unfold Array2.mixed_def.
  dump_pre_spatial.
  rewrite (Znth_indep matrix_mem i __default__List__App_option_Z nil) by lia.
  exists (Znth j (Znth i matrix nil) 0).
  apply PreH21; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_12_pure_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite staged_ops_nil__initialization.
  sep_apply_l_atomic
    (IntArray.undef_full_to_mixed_full ops_pre 5000).
  replace (Z.to_nat 5000) with (5000%nat) by reflexivity.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
Qed.
