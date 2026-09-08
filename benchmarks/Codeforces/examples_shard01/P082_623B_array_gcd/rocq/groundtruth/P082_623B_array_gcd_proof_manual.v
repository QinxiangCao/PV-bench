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
Require Import PVbench.Codeforces.examples_shard01.P082_623B_array_gcd.rocq.groundtruth.P082_623B_array_gcd_goal.
Require Import PVbench.Codeforces.examples_shard01.P082_623B_array_gcd.rocq.groundtruth.P082_623B_array_gcd_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import PVbench.Codeforces.examples_shard01.P082_623B_array_gcd.rocq.groundtruth.proof_lib.
Local Open Scope sac.

Lemma proof_of_add_factors_entail_wit_1 : add_factors_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists all_2 (@nil Z).
  rewrite Zlength_nil.
  replace (k0 + 0) with k0 by lia.
  rewrite app_nil_r.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    subst v_pre. apply scan_init__addfac_scan_invariant. lia.
Qed.

Lemma proof_of_add_factors_entail_wit_2 : add_factors_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  Exists (replace_Znth (k0 + Zlength fs_2) d all_2) (fs_2 ++ (d :: nil)).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (k0 + (Zlength fs_2 + Z.succ 0)) with (k0 + Zlength fs_2 + 1) by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + rewrite Zlength_replace_Znth. exact PreH14.
    + rewrite replace_Znth_sublist_append__addfac_scan_invariant by lia.
      rewrite PreH15, app_assoc. reflexivity.
    + apply scan_to_extract__addfac_scan_invariant; try assumption; try lia.
      apply (proj1 (rem_zero_iff_divide__addfac_scan_invariant v d ltac:(lia) ltac:(lia))).
      exact PreH1.
Qed.

Lemma proof_of_add_factors_entail_wit_3_1 : add_factors_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hd0 : d <> 0) by lia.
  pose proof (Z.quot_rem v d Hd0) as Hqr.
  rewrite PreH1 in Hqr.
  set (w := v ÷ d) in *.
  assert (Hvw : v = d * w) by lia.
  assert (Hw1 : 1 <= w) by nia.
  assert (Hwlev : w <= v) by nia.
  assert (Hwv0 : w <= v0) by lia.
  assert (Hwv : Z.divide w v) by (exists d; lia).
  destruct PreH16 as [HF [Hscan [Hd2 [Hin Hbound]]]].
  assert (HFw : FactorsSoFar v0 w fs_2).
  { apply (factors_so_far_quot__addfac_division_residual v0 v d w fs_2); auto. }
  assert (Hscanw : forall q, 2 <= q -> q < d -> ~ Z.divide q w).
  { intros q Hq1 Hq2 Hqw. apply (Hscan q Hq1 Hq2).
    apply (Z.divide_trans q w v); assumption. }
  assert (Hpow : 0 <= 2 ^ (Zlength fs_2 - 1)) by (apply Z.pow_nonneg; lia).
  assert (Hextract : AddFactorsExtract v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    split; [ lia | ]. split; [ exact Hin | ]. nia. }
  assert (Hscanres : AddFactorsScan v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    apply (doubling_bound_quot__addfac_division_residual
             (Zlength fs_2) v0 v d w); try assumption; lia. }
  Right.
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [ assumption | lia ].
Qed.

Lemma proof_of_add_factors_entail_wit_3_2 : add_factors_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hd0 : d <> 0) by lia.
  pose proof (Z.quot_rem v d Hd0) as Hqr.
  rewrite PreH1 in Hqr.
  set (w := v ÷ d) in *.
  assert (Hvw : v = d * w) by lia.
  assert (Hw1 : 1 <= w) by nia.
  assert (Hwlev : w <= v) by nia.
  assert (Hwv0 : w <= v0) by lia.
  assert (Hwv : Z.divide w v) by (exists d; lia).
  destruct PreH16 as [HF [Hscan [Hd2 [Hin Hbound]]]].
  assert (HFw : FactorsSoFar v0 w fs_2).
  { apply (factors_so_far_quot__addfac_division_residual v0 v d w fs_2); auto. }
  assert (Hscanw : forall q, 2 <= q -> q < d -> ~ Z.divide q w).
  { intros q Hq1 Hq2 Hqw. apply (Hscan q Hq1 Hq2).
    apply (Z.divide_trans q w v); assumption. }
  assert (Hpow : 0 <= 2 ^ (Zlength fs_2 - 1)) by (apply Z.pow_nonneg; lia).
  assert (Hextract : AddFactorsExtract v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    split; [ lia | ]. split; [ exact Hin | ]. nia. }
  assert (Hscanres : AddFactorsScan v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    apply (doubling_bound_quot__addfac_division_residual
             (Zlength fs_2) v0 v d w); try assumption; lia. }
  Right.
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [ assumption | lia ].
Qed.

Lemma proof_of_add_factors_entail_wit_4 : add_factors_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH15 as [HF [Hscan Hbound]].
  assert (Hres : AddFactorsResidual v0 v fs_2).
  { split; [ exact HF | ]. split; [ | exact Hbound ].
    apply (residual_is_one_or_prime__addfac_division_residual v d);
      try assumption; lia. }
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [ assumption | lia ].
Qed.

Lemma proof_of_add_factors_entail_wit_5_1 : add_factors_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + destruct PreH17 as [_ [_ Hb]].
      apply (scan_length_bound__addfac_scan_invariant v0 v (Zlength fs_2)); lia.
    + apply scan_step_divisor__addfac_scan_invariant; assumption.
Qed.

Lemma proof_of_add_factors_entail_wit_5_2 : add_factors_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply scan_step_divisor__addfac_scan_invariant; assumption.
Qed.

Lemma proof_of_add_factors_return_wit_1 : add_factors_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hz : Zlength (fs_2 ++ (cons v nil)) = Zlength fs_2 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hsub : sublist 0 (k0 + Zlength fs_2 + 1)
                   (replace_Znth (k0 + Zlength fs_2) v all)
                 = app pre (fs_2 ++ (cons v nil))).
  { rewrite sublist_replace_Znth_snoc__addfac_frame_result
      by (rewrite PreH11; lia).
    rewrite PreH12.
    rewrite <- app_assoc.
    reflexivity. }
  assert (Hres : AddFactorsResult v0 (fs_2 ++ (cons v nil)))
    by (apply (add_factors_result_append_prime__addfac_frame_result v0 v fs_2);
        [ exact PreH13 | lia | lia ]).
  Exists (fs_2 ++ (cons v nil)).
  rewrite Hz.
  replace (k0 + (Zlength fs_2 + 1)) with (k0 + Zlength fs_2 + 1) by lia.
  rewrite Hsub.
  entailer_with ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_add_factors_return_wit_2 : add_factors_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hres : AddFactorsResult v0 fs_2)
    by (apply (add_factors_result_of_residual_one__addfac_frame_result v0 v fs_2);
        [ exact PreH13 | lia | lia ]).
  Exists fs_2.
  rewrite PreH12.
  entailer_with ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_add_factors_partial_solve_wit_5_pure_split_goal_1 : add_factors_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_add_factors_partial_solve_wit_5_pure : add_factors_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_factors_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_add_factors_which_implies_wit_1 : add_factors_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Haux : forall (n : nat) (x lo hi : Z),
            hi - lo = Z.of_nat n ->
            Int64Array.seg_shape x lo hi |-- EX l : list Z, Int64Array.seg x lo hi l).
  { induction n; intros x lo hi Hn.
    - assert (hi = lo) by lia. subst hi.
      rewrite Int64Array.seg_shape_empty.
      Exists (@nil Z).
      rewrite Int64Array.seg_empty.
      entailer_with ltac:(lia || nia || int_auto).
    - rewrite (Int64Array.seg_shape_unfold x lo hi) by lia.
      Intros a.
      sep_apply (IHn x (lo + 1) hi); try lia.
      Intros l.
      Exists (a :: l).
      rewrite (Int64Array.seg_unfold x lo hi l a).
      cancel. }
  sep_apply (Haux (Z.to_nat (256 - k0)) primes k0 256); try lia.
  Intros tail.
  prop_apply (Int64Array.seg_Zlength primes k0 256 tail).
  Intros.
  Exists (app pre tail).
  sep_apply (Int64Array.seg_merge_to_full primes 0 k0 256 pre tail); try lia.
  rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r.
  assert (Hs : sublist 0 k0 (app pre tail) = pre).
  { rewrite <- PreH3. apply sublist_app_exact1. }
  assert (Hz : Zlength (app pre tail) = 256).
  { rewrite Zlength_app. lia. }
  rewrite Hs, Hz.
  entailer_with ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_add_factors_which_implies_wit_2_split_goal_spatial : add_factors_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (Int64Array.full_split_to_seg primes m 256 all); try lia.
  sep_apply (Int64Array.seg_to_seg_shape primes m 256 (sublist m 256 all)).
  cancel.
Qed.

Lemma proof_of_add_factors_which_implies_wit_2 : add_factors_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_factors_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1_split_goal_1 : cost_for_prime_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply cost_for_prime_state_init__cfp_core_init_elemcost.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1_split_goal_2 : cost_for_prime_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1 : cost_for_prime_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1_split_goal_1 : cost_for_prime_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH10 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE1; exact PreH1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1_split_goal_2 : cost_for_prime_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH10; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1 : cost_for_prime_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2_split_goal_1 : cost_for_prime_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH11 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE2; [exact PreH2 | exact PreH1].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2_split_goal_2 : cost_for_prime_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2 : cost_for_prime_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3_split_goal_1 : cost_for_prime_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH12 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE3; [exact PreH3 | exact PreH2 | exact PreH1].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3_split_goal_2 : cost_for_prime_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3 : cost_for_prime_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4_split_goal_1 : cost_for_prime_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH12 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE4; [exact PreH3 | exact PreH2 | exact PreH1].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4_split_goal_2 : cost_for_prime_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4 : cost_for_prime_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_4_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1_split_goal_1 : cost_for_prime_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1_split_goal_2 : cost_for_prime_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1_split_goal_3 : cost_for_prime_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1_split_goal_4 : cost_for_prime_entail_wit_3_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1_split_goal_5 : cost_for_prime_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1 : cost_for_prime_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_1_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_1_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_1_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_1_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_1 : cost_for_prime_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply cfp_state_step__cfp_step_06; try assumption; try lia; try congruence.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_2 : cost_for_prime_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_3 : cost_for_prime_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_4 : cost_for_prime_entail_wit_3_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_5 : cost_for_prime_entail_wit_3_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_6 : cost_for_prime_entail_wit_3_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall x : Z, _ -> (2 <= Znth x _ 0 /\ _) |- _ =>
      first [ apply H; lia | intros ? ?; apply H; lia ]
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2 : cost_for_prime_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_3_split_goal_1 : cost_for_prime_entail_wit_3_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply cfp_state_step__cfp_step_06; try assumption; try lia; try congruence.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_3_split_goal_2 : cost_for_prime_entail_wit_3_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_3_split_goal_3 : cost_for_prime_entail_wit_3_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_3_split_goal_4 : cost_for_prime_entail_wit_3_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_3_split_goal_5 : cost_for_prime_entail_wit_3_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_3_split_goal_6 : cost_for_prime_entail_wit_3_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall x : Z, _ -> (2 <= Znth x _ 0 /\ _) |- _ =>
      first [ apply H; lia | intros ? ?; apply H; lia ]
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_3 : cost_for_prime_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_3_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_3_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_3_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_3_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_3_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_3_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_4_split_goal_1 : cost_for_prime_entail_wit_3_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_4_split_goal_2 : cost_for_prime_entail_wit_3_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_4_split_goal_3 : cost_for_prime_entail_wit_3_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_4_split_goal_4 : cost_for_prime_entail_wit_3_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_4 : cost_for_prime_entail_wit_3_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_4_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_4_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_4_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_4_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_5_split_goal_1 : cost_for_prime_entail_wit_3_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutafterkeep_zero_inf__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_5_split_goal_2 : cost_for_prime_entail_wit_3_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutafterkeep_zero_inf__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_5_split_goal_3 : cost_for_prime_entail_wit_3_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutafterkeep_zero_inf__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_5_split_goal_4 : cost_for_prime_entail_wit_3_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutafterkeep_zero_inf__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_5_split_goal_5 : cost_for_prime_entail_wit_3_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH19 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_5 : cost_for_prime_entail_wit_3_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_5_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_5_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_5_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_5_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_5_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_6_split_goal_1 : cost_for_prime_entail_wit_3_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_6_split_goal_2 : cost_for_prime_entail_wit_3_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_6_split_goal_3 : cost_for_prime_entail_wit_3_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_6_split_goal_4 : cost_for_prime_entail_wit_3_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_6 : cost_for_prime_entail_wit_3_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_6_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_6_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_6_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_6_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_7_split_goal_1 : cost_for_prime_entail_wit_3_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_7_split_goal_2 : cost_for_prime_entail_wit_3_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_7_split_goal_3 : cost_for_prime_entail_wit_3_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_7 : cost_for_prime_entail_wit_3_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_7_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_7_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_7_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_8_split_goal_1 : cost_for_prime_entail_wit_3_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_8_split_goal_2 : cost_for_prime_entail_wit_3_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_8_split_goal_3 : cost_for_prime_entail_wit_3_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_8_split_goal_4 : cost_for_prime_entail_wit_3_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_8 : cost_for_prime_entail_wit_3_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_8_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_8_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_8_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_8_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_9_split_goal_1 : cost_for_prime_entail_wit_3_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_9_split_goal_2 : cost_for_prime_entail_wit_3_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_9_split_goal_3 : cost_for_prime_entail_wit_3_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      replace i with 0 in H by lia;
      pose proof (cfp_state_zero_cak_inf__cfp_step_06 a d c p _ _ _ _ H) as Hz
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_9 : cost_for_prime_entail_wit_3_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_9_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_9_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_9_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_10_split_goal_1 : cost_for_prime_entail_wit_3_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_10_split_goal_2 : cost_for_prime_entail_wit_3_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_10_split_goal_3 : cost_for_prime_entail_wit_3_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_10 : cost_for_prime_entail_wit_3_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_10_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_10_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_10_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_11_split_goal_1 : cost_for_prime_entail_wit_3_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply cfp_state_step_inf_keep__cfp_step_06; try eassumption; try lia; try congruence.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_11_split_goal_2 : cost_for_prime_entail_wit_3_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_11_split_goal_3 : cost_for_prime_entail_wit_3_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall x : Z, _ -> (2 <= Znth x _ 0 /\ _) |- _ =>
      first [ apply H; lia | intros ? ?; apply H; lia ]
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_11 : cost_for_prime_entail_wit_3_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_11_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_11_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_11_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_12_split_goal_1 : cost_for_prime_entail_wit_3_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply cfp_state_step_inf_keep__cfp_step_06; try eassumption; try lia; try congruence.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_12_split_goal_2 : cost_for_prime_entail_wit_3_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_12_split_goal_3 : cost_for_prime_entail_wit_3_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      destruct (cfp_state_finite_bound__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
        as [Hbk [Hbf [Hbc Hba]]];
      try specialize (Hbk ltac:(lia));
      try specialize (Hbf ltac:(lia));
      try specialize (Hbc ltac:(lia));
      try specialize (Hba ltac:(lia))
  end;
  match goal with
  | H : ?cst = ElemCost ?ch ?pp ?vv |- _ =>
      pose proof (elem_cost_bound__cfp_step_06 ch pp vv ltac:(lia)
        ltac:(rewrite <- H; lia)) as Hec;
      rewrite <- H in Hec
  end;
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_12_split_goal_4 : cost_for_prime_entail_wit_3_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall x : Z, _ -> (2 <= Znth x _ 0 /\ _) |- _ =>
      first [ apply H; lia | intros ? ?; apply H; lia ]
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_12 : cost_for_prime_entail_wit_3_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_12_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_12_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_12_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_12_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_13_split_goal_1 : cost_for_prime_entail_wit_3_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  apply (cfp_state_step__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after cost);
    unfold INF in *; try assumption; try lia; try nia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_13_split_goal_2 : cost_for_prime_entail_wit_3_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_13_split_goal_3 : cost_for_prime_entail_wit_3_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_13_split_goal_4 : cost_for_prime_entail_wit_3_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_13 : cost_for_prime_entail_wit_3_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_13_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_13_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_13_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_13_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_14_split_goal_1 : cost_for_prime_entail_wit_3_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_14_split_goal_2 : cost_for_prime_entail_wit_3_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_14_split_goal_3 : cost_for_prime_entail_wit_3_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_14_split_goal_4 : cost_for_prime_entail_wit_3_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_14 : cost_for_prime_entail_wit_3_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_14_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_14_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_14_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_14_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_15_split_goal_1 : cost_for_prime_entail_wit_3_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_15_split_goal_2 : cost_for_prime_entail_wit_3_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_15_split_goal_3 : cost_for_prime_entail_wit_3_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_15_split_goal_4 : cost_for_prime_entail_wit_3_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_15_split_goal_5 : cost_for_prime_entail_wit_3_15_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_15 : cost_for_prime_entail_wit_3_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_15_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_15_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_15_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_15_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_15_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_16_split_goal_1 : cost_for_prime_entail_wit_3_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      exact (cfp_state_step__cfp_step_07 values a_pre b_pre p_pre i keep cutFresh
               cutAfterKeep after cost HS
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(try subst v; assumption)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia))
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_16_split_goal_2 : cost_for_prime_entail_wit_3_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_16_split_goal_3 : cost_for_prime_entail_wit_3_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_16_split_goal_4 : cost_for_prime_entail_wit_3_16_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_16_split_goal_5 : cost_for_prime_entail_wit_3_16_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_16_split_goal_6 : cost_for_prime_entail_wit_3_16_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH19 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_16 : cost_for_prime_entail_wit_3_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_16_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_16_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_16_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_16_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_16_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_16_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_17_split_goal_1 : cost_for_prime_entail_wit_3_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_17_split_goal_2 : cost_for_prime_entail_wit_3_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_17_split_goal_3 : cost_for_prime_entail_wit_3_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_17_split_goal_4 : cost_for_prime_entail_wit_3_17_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_17_split_goal_5 : cost_for_prime_entail_wit_3_17_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH20 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_17 : cost_for_prime_entail_wit_3_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_17_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_17_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_17_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_17_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_17_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_18_split_goal_1 : cost_for_prime_entail_wit_3_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      exact (cfp_state_step__cfp_step_07 values a_pre b_pre p_pre i keep cutFresh
               cutAfterKeep after cost HS
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(try subst v; assumption)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia))
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_18_split_goal_2 : cost_for_prime_entail_wit_3_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_18_split_goal_3 : cost_for_prime_entail_wit_3_18_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_18_split_goal_4 : cost_for_prime_entail_wit_3_18_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_18_split_goal_5 : cost_for_prime_entail_wit_3_18_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_18_split_goal_6 : cost_for_prime_entail_wit_3_18_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH20 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_18 : cost_for_prime_entail_wit_3_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_18_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_18_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_18_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_18_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_18_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_18_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_19_split_goal_1 : cost_for_prime_entail_wit_3_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      exact (cfp_state_step__cfp_step_07 values a_pre b_pre p_pre i keep cutFresh
               cutAfterKeep after cost HS
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(try subst v; assumption)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia))
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_19_split_goal_2 : cost_for_prime_entail_wit_3_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_19_split_goal_3 : cost_for_prime_entail_wit_3_19_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_19_split_goal_4 : cost_for_prime_entail_wit_3_19_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_19_split_goal_5 : cost_for_prime_entail_wit_3_19_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk ltac:(lia)) as Hk.
  pose proof (Hbf ltac:(lia)) as Hf.
  pose proof (Hbt ltac:(lia)) as Ht.
  assert (Hec : 0 <= cost <= b_pre).
  { subst cost. apply elemcost_bound__cfp_step_07; lia. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_19_split_goal_6 : cost_for_prime_entail_wit_3_19_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH20 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_19 : cost_for_prime_entail_wit_3_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_19_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_19_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_19_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_19_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_19_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_19_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_20_split_goal_1 : cost_for_prime_entail_wit_3_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_20_split_goal_2 : cost_for_prime_entail_wit_3_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_20_split_goal_3 : cost_for_prime_entail_wit_3_20_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_20_split_goal_4 : cost_for_prime_entail_wit_3_20_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_20_split_goal_5 : cost_for_prime_entail_wit_3_20_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_20 : cost_for_prime_entail_wit_3_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_20_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_20_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_20_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_20_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_20_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_21_split_goal_1 : cost_for_prime_entail_wit_3_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_21_split_goal_2 : cost_for_prime_entail_wit_3_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_21_split_goal_3 : cost_for_prime_entail_wit_3_21_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_21_split_goal_4 : cost_for_prime_entail_wit_3_21_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_21_split_goal_5 : cost_for_prime_entail_wit_3_21_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_21 : cost_for_prime_entail_wit_3_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_21_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_21_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_21_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_21_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_21_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_22_split_goal_1 : cost_for_prime_entail_wit_3_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_22_split_goal_2 : cost_for_prime_entail_wit_3_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_22_split_goal_3 : cost_for_prime_entail_wit_3_22_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_22_split_goal_4 : cost_for_prime_entail_wit_3_22_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_22 : cost_for_prime_entail_wit_3_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_22_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_22_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_22_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_22_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_23_split_goal_1 : cost_for_prime_entail_wit_3_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_23_split_goal_2 : cost_for_prime_entail_wit_3_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_23_split_goal_3 : cost_for_prime_entail_wit_3_23_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_23_split_goal_4 : cost_for_prime_entail_wit_3_23_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_23 : cost_for_prime_entail_wit_3_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_23_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_23_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_23_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_23_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_24_split_goal_1 : cost_for_prime_entail_wit_3_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_24_split_goal_2 : cost_for_prime_entail_wit_3_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_24_split_goal_3 : cost_for_prime_entail_wit_3_24_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_24_split_goal_4 : cost_for_prime_entail_wit_3_24_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_24 : cost_for_prime_entail_wit_3_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_24_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_24_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_24_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_24_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_25_split_goal_1 : cost_for_prime_entail_wit_3_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_25_split_goal_2 : cost_for_prime_entail_wit_3_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_25_split_goal_3 : cost_for_prime_entail_wit_3_25_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_25 : cost_for_prime_entail_wit_3_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_25_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_25_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_25_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_26_split_goal_1 : cost_for_prime_entail_wit_3_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_26_split_goal_2 : cost_for_prime_entail_wit_3_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_26_split_goal_3 : cost_for_prime_entail_wit_3_26_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_26 : cost_for_prime_entail_wit_3_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_26_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_26_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_26_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_27_split_goal_1 : cost_for_prime_entail_wit_3_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  apply (cfp_state_step__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after cost);
    unfold INF in *; try assumption; try lia; try nia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_27_split_goal_2 : cost_for_prime_entail_wit_3_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_27_split_goal_3 : cost_for_prime_entail_wit_3_27_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_27_split_goal_4 : cost_for_prime_entail_wit_3_27_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_27 : cost_for_prime_entail_wit_3_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_27_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_27_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_27_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_27_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_28_split_goal_1 : cost_for_prime_entail_wit_3_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  apply (cfp_state_step__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after cost);
    unfold INF in *; try assumption; try lia; try nia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_28_split_goal_2 : cost_for_prime_entail_wit_3_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_28_split_goal_3 : cost_for_prime_entail_wit_3_28_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  assert (HBnd : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= 1000000000).
  { destruct (elemcost_cases__cfp_step_05 b_pre p_pre (Znth i values 0)) as [HE | [HE | HE]];
    unfold INF in *; lia. }
  destruct (cfp_state_finite_bound__cfp_step_05 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) ltac:(assumption)) as [Bk [Bf [Bc Ba]]].
  specialize (Bf ltac:(unfold INF; lia)).
  specialize (Ba ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_28_split_goal_4 : cost_for_prime_entail_wit_3_28_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_28 : cost_for_prime_entail_wit_3_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_28_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_28_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_28_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_28_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_29_split_goal_1 : cost_for_prime_entail_wit_3_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_29_split_goal_2 : cost_for_prime_entail_wit_3_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_29 : cost_for_prime_entail_wit_3_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_29_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_29_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_30_split_goal_1 : cost_for_prime_entail_wit_3_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_30_split_goal_2 : cost_for_prime_entail_wit_3_30_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_30 : cost_for_prime_entail_wit_3_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_30_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_30_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_31_split_goal_1 : cost_for_prime_entail_wit_3_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_31_split_goal_2 : cost_for_prime_entail_wit_3_31_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_31_split_goal_3 : cost_for_prime_entail_wit_3_31_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso;
       assert (HX : after = INF) by (eapply cfp_after_zero__cfp_step_05; [eassumption | lia]);
       unfold INF in HX; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_31 : cost_for_prime_entail_wit_3_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_31_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_31_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_31_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_32_split_goal_1 : cost_for_prime_entail_wit_3_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_32_split_goal_2 : cost_for_prime_entail_wit_3_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_32_split_goal_3 : cost_for_prime_entail_wit_3_32_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_32_split_goal_4 : cost_for_prime_entail_wit_3_32_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH19 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_32 : cost_for_prime_entail_wit_3_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_32_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_32_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_32_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_32_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_33_split_goal_1 : cost_for_prime_entail_wit_3_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_33_split_goal_2 : cost_for_prime_entail_wit_3_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_33_split_goal_3 : cost_for_prime_entail_wit_3_33_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_33_split_goal_4 : cost_for_prime_entail_wit_3_33_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_33 : cost_for_prime_entail_wit_3_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_33_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_33_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_33_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_33_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_34_split_goal_1 : cost_for_prime_entail_wit_3_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH35)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_34_split_goal_2 : cost_for_prime_entail_wit_3_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH35)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_34_split_goal_3 : cost_for_prime_entail_wit_3_34_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH17. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_34 : cost_for_prime_entail_wit_3_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_34_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_34_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_34_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_35_split_goal_1 : cost_for_prime_entail_wit_3_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_35_split_goal_2 : cost_for_prime_entail_wit_3_35_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH16; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_35 : cost_for_prime_entail_wit_3_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_35_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_35_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_36_split_goal_1 : cost_for_prime_entail_wit_3_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_36_split_goal_2 : cost_for_prime_entail_wit_3_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH17; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_36 : cost_for_prime_entail_wit_3_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_36_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_36_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_37_split_goal_1 : cost_for_prime_entail_wit_3_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hba ltac:(lia)) as Hca.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_37_split_goal_2 : cost_for_prime_entail_wit_3_37_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hba ltac:(lia)) as Hca.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_37_split_goal_3 : cost_for_prime_entail_wit_3_37_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  destruct Hst as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hba ltac:(lia)) as Hca.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_37_split_goal_4 : cost_for_prime_entail_wit_3_37_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH18 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_37 : cost_for_prime_entail_wit_3_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_37_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_37_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_37_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_37_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_38_split_goal_1 : cost_for_prime_entail_wit_3_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH36)
    as [_ [_ [Hba _]]].
  rewrite Hz in Hba.
  specialize (Hba ltac:(unfold INF; lia)).
  assert (Hprod : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_38_split_goal_2 : cost_for_prime_entail_wit_3_38_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH36)
    as [_ [_ [Hba _]]].
  rewrite Hz in Hba.
  specialize (Hba ltac:(unfold INF; lia)).
  assert (Hprod : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_38_split_goal_3 : cost_for_prime_entail_wit_3_38_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH36)
    as [_ [_ [Hba _]]].
  rewrite Hz in Hba.
  specialize (Hba ltac:(unfold INF; lia)).
  assert (Hprod : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_38_split_goal_4 : cost_for_prime_entail_wit_3_38_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH36)
    as [_ [_ [Hba _]]].
  rewrite Hz in Hba.
  specialize (Hba ltac:(unfold INF; lia)).
  assert (Hprod : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_38 : cost_for_prime_entail_wit_3_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_38_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_38_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_38_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_38_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_39_split_goal_1 : cost_for_prime_entail_wit_3_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_39_split_goal_2 : cost_for_prime_entail_wit_3_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_39_split_goal_3 : cost_for_prime_entail_wit_3_39_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH18 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_39 : cost_for_prime_entail_wit_3_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_39_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_39_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_39_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_40_split_goal_1 : cost_for_prime_entail_wit_3_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_40_split_goal_2 : cost_for_prime_entail_wit_3_40_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_40_split_goal_3 : cost_for_prime_entail_wit_3_40_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH17 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_40 : cost_for_prime_entail_wit_3_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_40_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_40_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_40_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_41_split_goal_1 : cost_for_prime_entail_wit_3_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_41_split_goal_2 : cost_for_prime_entail_wit_3_41_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_41_split_goal_3 : cost_for_prime_entail_wit_3_41_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_41_split_goal_4 : cost_for_prime_entail_wit_3_41_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_41 : cost_for_prime_entail_wit_3_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_41_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_41_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_41_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_41_split_goal_4.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_42_split_goal_1 : cost_for_prime_entail_wit_3_42_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_42_split_goal_2 : cost_for_prime_entail_wit_3_42_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_42_split_goal_3 : cost_for_prime_entail_wit_3_42_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_42_split_goal_4 : cost_for_prime_entail_wit_3_42_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_42 : cost_for_prime_entail_wit_3_42.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_42_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_42_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_42_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_42_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_43_split_goal_1 : cost_for_prime_entail_wit_3_43_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_43_split_goal_2 : cost_for_prime_entail_wit_3_43_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_43_split_goal_3 : cost_for_prime_entail_wit_3_43_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_43_split_goal_4 : cost_for_prime_entail_wit_3_43_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_43 : cost_for_prime_entail_wit_3_43.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_43_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_43_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_43_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_43_split_goal_4.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_44_split_goal_1 : cost_for_prime_entail_wit_3_44_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_44_split_goal_2 : cost_for_prime_entail_wit_3_44_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_44_split_goal_3 : cost_for_prime_entail_wit_3_44_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_44_split_goal_4 : cost_for_prime_entail_wit_3_44_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_44_split_goal_5 : cost_for_prime_entail_wit_3_44_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_44 : cost_for_prime_entail_wit_3_44.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_44_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_44_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_44_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_44_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_44_split_goal_5.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_45_split_goal_1 : cost_for_prime_entail_wit_3_45_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_45_split_goal_2 : cost_for_prime_entail_wit_3_45_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_45_split_goal_3 : cost_for_prime_entail_wit_3_45_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_45_split_goal_4 : cost_for_prime_entail_wit_3_45_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_45_split_goal_5 : cost_for_prime_entail_wit_3_45_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_45 : cost_for_prime_entail_wit_3_45.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_45_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_45_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_45_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_45_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_45_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_46_split_goal_1 : cost_for_prime_entail_wit_3_46_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [Hk [_ [_ Haf]]].
  pose proof (dpafter_le_dpkeep__cfp_step_10 values a_pre b_pre p_pre i keep after
                ltac:(lia) ltac:(lia) Hk Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_46_split_goal_2 : cost_for_prime_entail_wit_3_46_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [Hk [_ [_ Haf]]].
  pose proof (dpafter_le_dpkeep__cfp_step_10 values a_pre b_pre p_pre i keep after
                ltac:(lia) ltac:(lia) Hk Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_46_split_goal_3 : cost_for_prime_entail_wit_3_46_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [Hk [_ [_ Haf]]].
  pose proof (dpafter_le_dpkeep__cfp_step_10 values a_pre b_pre p_pre i keep after
                ltac:(lia) ltac:(lia) Hk Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_46_split_goal_4 : cost_for_prime_entail_wit_3_46_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [Hk [_ [_ Haf]]].
  pose proof (dpafter_le_dpkeep__cfp_step_10 values a_pre b_pre p_pre i keep after
                ltac:(lia) ltac:(lia) Hk Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_46_split_goal_5 : cost_for_prime_entail_wit_3_46_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [Hk [_ [_ Haf]]].
  pose proof (dpafter_le_dpkeep__cfp_step_10 values a_pre b_pre p_pre i keep after
                ltac:(lia) ltac:(lia) Hk Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_46_split_goal_6 : cost_for_prime_entail_wit_3_46_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [Hk [_ [_ Haf]]].
  pose proof (dpafter_le_dpkeep__cfp_step_10 values a_pre b_pre p_pre i keep after
                ltac:(lia) ltac:(lia) Hk Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_46 : cost_for_prime_entail_wit_3_46.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_46_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_46_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_46_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_46_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_46_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_46_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_47_split_goal_1 : cost_for_prime_entail_wit_3_47_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  assert (Hce : cost = ElemCost b_pre p_pre (Znth i values 0)) by
    (rewrite Hce0, Hvi; reflexivity).
  assert (Hm1 : Z.min keep cutAfterKeep = keep) by (apply Z.min_l; lia).
  assert (Hm2 : Z.min (Z.min cutFresh cutAfterKeep) after = cutFresh).
  { rewrite (Z.min_l cutFresh cutAfterKeep) by lia. apply Z.min_l. lia. }
  replace (keep + a_pre) with (Z.min keep cutAfterKeep + a_pre) by lia.
  replace (cutFresh + cost) with
    (Z.min (Z.min cutFresh cutAfterKeep) after + cost) by lia.
  apply (cfp_state_step__cfp_step_12 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption; try (unfold INF in *; lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_47_split_goal_2 : cost_for_prime_entail_wit_3_47_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_47_split_goal_3 : cost_for_prime_entail_wit_3_47_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_47_split_goal_4 : cost_for_prime_entail_wit_3_47_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_47_split_goal_5 : cost_for_prime_entail_wit_3_47_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_47_split_goal_6 : cost_for_prime_entail_wit_3_47_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : forall j0 : Z, 0 <= j0 /\ j0 < n_pre ->
            2 <= Znth j0 values 0 /\ Znth j0 values 0 <= 1000000000) by assumption.
  apply Hrange; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_47 : cost_for_prime_entail_wit_3_47.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_47_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_47_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_47_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_47_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_47_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_47_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_48_split_goal_1 : cost_for_prime_entail_wit_3_48_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_48_split_goal_2 : cost_for_prime_entail_wit_3_48_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_48_split_goal_3 : cost_for_prime_entail_wit_3_48_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_48_split_goal_4 : cost_for_prime_entail_wit_3_48_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_48_split_goal_5 : cost_for_prime_entail_wit_3_48_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH37 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_48 : cost_for_prime_entail_wit_3_48.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_48_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_48_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_48_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_48_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_48_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_49_split_goal_1 : cost_for_prime_entail_wit_3_49_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  assert (Hce : cost = ElemCost b_pre p_pre (Znth i values 0)) by
    (rewrite Hce0, Hvi; reflexivity).
  assert (Hm1 : Z.min keep cutAfterKeep = keep) by (apply Z.min_l; lia).
  assert (Hm2 : Z.min (Z.min cutFresh cutAfterKeep) after = cutFresh).
  { rewrite (Z.min_l cutFresh cutAfterKeep) by lia. apply Z.min_l. lia. }
  replace (keep + a_pre) with (Z.min keep cutAfterKeep + a_pre) by lia.
  replace (cutFresh + cost) with
    (Z.min (Z.min cutFresh cutAfterKeep) after + cost) by lia.
  apply (cfp_state_step__cfp_step_12 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption; try (unfold INF in *; lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_49_split_goal_2 : cost_for_prime_entail_wit_3_49_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_49_split_goal_3 : cost_for_prime_entail_wit_3_49_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_49_split_goal_4 : cost_for_prime_entail_wit_3_49_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_49_split_goal_5 : cost_for_prime_entail_wit_3_49_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_49_split_goal_6 : cost_for_prime_entail_wit_3_49_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : forall j0 : Z, 0 <= j0 /\ j0 < n_pre ->
            2 <= Znth j0 values 0 /\ Znth j0 values 0 <= 1000000000) by assumption.
  apply Hrange; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_49 : cost_for_prime_entail_wit_3_49.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_49_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_49_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_49_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_49_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_49_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_49_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_50_split_goal_1 : cost_for_prime_entail_wit_3_50_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf,
    HE : ?cst = ElemCost _ _ _ |- _ =>
      apply (cfp_state_step__cfp_step_11 aa dd cc pp ii kk ff akak afaf cst _ _)
  end.
  2: { left. split; [reflexivity | left; lia]. }
  1: { left. split; [reflexivity | split; unfold INF in *; lia]. }
  all: try (unfold INF in *; lia).
  all: try assumption.
  all: match goal with
       | HE : _ = ElemCost _ _ _ |- _ => rewrite HE
       end;
       match goal with
       | Hv : _ = Znth _ _ 0 |- _ => rewrite Hv
       end;
       reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_50_split_goal_2 : cost_for_prime_entail_wit_3_50_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_50_split_goal_3 : cost_for_prime_entail_wit_3_50_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_50_split_goal_4 : cost_for_prime_entail_wit_3_50_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_50_split_goal_5 : cost_for_prime_entail_wit_3_50_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: repeat match goal with
              | H : _ /\ _ |- _ => destruct H
              end.
  all: match goal with
       | H : context[Znth _ _ 0] |- _ => apply H; lia
       end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_50 : cost_for_prime_entail_wit_3_50.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_50_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_50_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_50_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_50_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_50_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_51_split_goal_1 : cost_for_prime_entail_wit_3_51_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH34 as [Hk _].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk
     (dpkeep_zero_mem__cfp_step_10 values a_pre b_pre p_pre (Zlength_nonneg values))) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_51_split_goal_2 : cost_for_prime_entail_wit_3_51_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH34 as [Hk _].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk
     (dpkeep_zero_mem__cfp_step_10 values a_pre b_pre p_pre (Zlength_nonneg values))) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_51_split_goal_3 : cost_for_prime_entail_wit_3_51_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH34 as [Hk _].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk
     (dpkeep_zero_mem__cfp_step_10 values a_pre b_pre p_pre (Zlength_nonneg values))) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_51_split_goal_4 : cost_for_prime_entail_wit_3_51_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH34 as [Hk _].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk
     (dpkeep_zero_mem__cfp_step_10 values a_pre b_pre p_pre (Zlength_nonneg values))) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_51 : cost_for_prime_entail_wit_3_51.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_51_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_51_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_51_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_51_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_52_split_goal_1 : cost_for_prime_entail_wit_3_52_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH35)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH24. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH24; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbf ltac:(unfold INF; lia)).
  apply (cfp_state_step__cfp_step_10 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption;
    try (intros; try (unfold INF in * ); lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_52_split_goal_2 : cost_for_prime_entail_wit_3_52_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH35)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH24. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH24; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_52_split_goal_3 : cost_for_prime_entail_wit_3_52_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH35)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH24. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH24; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_52_split_goal_4 : cost_for_prime_entail_wit_3_52_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH17; assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_52 : cost_for_prime_entail_wit_3_52.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_52_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_52_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_52_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_52_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_53_split_goal_1 : cost_for_prime_entail_wit_3_53_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  apply (cfp_state_step__cfp_step_09 values a_pre b_pre p_pre i
           keep cutFresh cutAfterKeep after cost (4611686018427387904)).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - assumption.
  - unfold INF; lia.
  - assumption.
  - unfold INF; lia.
  - unfold INF; lia.
  - lia.
  - lia.
  - lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - left; unfold INF; split; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_53_split_goal_2 : cost_for_prime_entail_wit_3_53_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_53_split_goal_3 : cost_for_prime_entail_wit_3_53_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_53_split_goal_4 : cost_for_prime_entail_wit_3_53_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_53 : cost_for_prime_entail_wit_3_53.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_53_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_53_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_53_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_53_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_54_split_goal_1 : cost_for_prime_entail_wit_3_54_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf,
    HE : ?cst = ElemCost _ _ _ |- _ =>
      apply (cfp_state_step__cfp_step_11 aa dd cc pp ii kk ff akak afaf cst _ _)
  end.
  2: { right. repeat split; first [reflexivity | unfold INF in *; lia]. }
  1: { right. split; [reflexivity | unfold INF in *; lia]. }
  all: try (unfold INF in *; lia).
  all: try assumption.
  all: match goal with
       | HE : _ = ElemCost _ _ _ |- _ => rewrite HE
       end;
       match goal with
       | Hv : _ = Znth _ _ 0 |- _ => rewrite Hv
       end;
       reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_54_split_goal_2 : cost_for_prime_entail_wit_3_54_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_54_split_goal_3 : cost_for_prime_entail_wit_3_54_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: repeat match goal with
              | H : _ /\ _ |- _ => destruct H
              end.
  all: match goal with
       | H : context[Znth _ _ 0] |- _ => apply H; lia
       end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_54 : cost_for_prime_entail_wit_3_54.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_54_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_54_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_54_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_55_split_goal_1 : cost_for_prime_entail_wit_3_55_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_55_split_goal_2 : cost_for_prime_entail_wit_3_55_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_55_split_goal_3 : cost_for_prime_entail_wit_3_55_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_55 : cost_for_prime_entail_wit_3_55.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_55_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_55_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_55_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_56_split_goal_1 : cost_for_prime_entail_wit_3_56_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_56_split_goal_2 : cost_for_prime_entail_wit_3_56_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_56_split_goal_3 : cost_for_prime_entail_wit_3_56_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_56 : cost_for_prime_entail_wit_3_56.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_56_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_56_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_56_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_57_split_goal_1 : cost_for_prime_entail_wit_3_57_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_57_split_goal_2 : cost_for_prime_entail_wit_3_57_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_57_split_goal_3 : cost_for_prime_entail_wit_3_57_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_57_split_goal_4 : cost_for_prime_entail_wit_3_57_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_57 : cost_for_prime_entail_wit_3_57.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_57_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_57_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_57_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_57_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_58_split_goal_1 : cost_for_prime_entail_wit_3_58_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_58_split_goal_2 : cost_for_prime_entail_wit_3_58_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_58_split_goal_3 : cost_for_prime_entail_wit_3_58_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_58 : cost_for_prime_entail_wit_3_58.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_58_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_58_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_58_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_59_split_goal_1 : cost_for_prime_entail_wit_3_59_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_59_split_goal_2 : cost_for_prime_entail_wit_3_59_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_59_split_goal_3 : cost_for_prime_entail_wit_3_59_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_59_split_goal_4 : cost_for_prime_entail_wit_3_59_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_59 : cost_for_prime_entail_wit_3_59.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_59_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_59_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_59_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_59_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_60_split_goal_1 : cost_for_prime_entail_wit_3_60_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_60_split_goal_2 : cost_for_prime_entail_wit_3_60_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_60_split_goal_3 : cost_for_prime_entail_wit_3_60_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_60_split_goal_4 : cost_for_prime_entail_wit_3_60_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_60_split_goal_5 : cost_for_prime_entail_wit_3_60_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_60 : cost_for_prime_entail_wit_3_60.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_60_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_60_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_60_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_60_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_60_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_61_split_goal_1 : cost_for_prime_entail_wit_3_61_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_61_split_goal_2 : cost_for_prime_entail_wit_3_61_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_61_split_goal_3 : cost_for_prime_entail_wit_3_61_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_61_split_goal_4 : cost_for_prime_entail_wit_3_61_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_61 : cost_for_prime_entail_wit_3_61.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_61_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_61_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_61_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_61_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_62_split_goal_1 : cost_for_prime_entail_wit_3_62_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  apply (cfp_state_step__cfp_step_09 values a_pre b_pre p_pre i
           keep cutFresh cutAfterKeep after cost (keep + cost)).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - assumption.
  - unfold INF; lia.
  - assumption.
  - unfold INF; lia.
  - unfold INF; lia.
  - lia.
  - lia.
  - lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - right; unfold INF; split; [lia | split; [reflexivity | lia]].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_62_split_goal_2 : cost_for_prime_entail_wit_3_62_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_62_split_goal_3 : cost_for_prime_entail_wit_3_62_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_62_split_goal_4 : cost_for_prime_entail_wit_3_62_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_62_split_goal_5 : cost_for_prime_entail_wit_3_62_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_62_split_goal_6 : cost_for_prime_entail_wit_3_62_split_goal_6.
Proof.
  LLM_pre_process ltac:(idtac).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_62 : cost_for_prime_entail_wit_3_62.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_62_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_62_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_62_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_62_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_62_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_62_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_63_split_goal_1 : cost_for_prime_entail_wit_3_63_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  assert (Hce : cost = ElemCost b_pre p_pre (Znth i values 0)) by
    (rewrite Hce0, Hvi; reflexivity).
  assert (Hm1 : Z.min keep cutAfterKeep = cutAfterKeep) by (apply Z.min_r; lia).
  assert (Hm2 : Z.min (Z.min cutFresh cutAfterKeep) after = cutFresh).
  { rewrite (Z.min_l cutFresh cutAfterKeep) by lia. apply Z.min_l. lia. }
  replace (cutAfterKeep + a_pre) with (Z.min keep cutAfterKeep + a_pre) by lia.
  replace (cutFresh + cost) with
    (Z.min (Z.min cutFresh cutAfterKeep) after + cost) by lia.
  apply (cfp_state_step__cfp_step_12 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption; try (unfold INF in *; lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_63_split_goal_2 : cost_for_prime_entail_wit_3_63_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_63_split_goal_3 : cost_for_prime_entail_wit_3_63_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_63_split_goal_4 : cost_for_prime_entail_wit_3_63_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_63_split_goal_5 : cost_for_prime_entail_wit_3_63_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_63_split_goal_6 : cost_for_prime_entail_wit_3_63_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : forall j0 : Z, 0 <= j0 /\ j0 < n_pre ->
            2 <= Znth j0 values 0 /\ Znth j0 values 0 <= 1000000000) by assumption.
  apply Hrange; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_63 : cost_for_prime_entail_wit_3_63.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_63_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_63_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_63_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_63_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_63_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_63_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_64_split_goal_1 : cost_for_prime_entail_wit_3_64_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_64_split_goal_2 : cost_for_prime_entail_wit_3_64_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_64_split_goal_3 : cost_for_prime_entail_wit_3_64_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_64_split_goal_4 : cost_for_prime_entail_wit_3_64_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_64_split_goal_5 : cost_for_prime_entail_wit_3_64_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_64 : cost_for_prime_entail_wit_3_64.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_64_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_64_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_64_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_64_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_64_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_65_split_goal_1 : cost_for_prime_entail_wit_3_65_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_65_split_goal_2 : cost_for_prime_entail_wit_3_65_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_65_split_goal_3 : cost_for_prime_entail_wit_3_65_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_65_split_goal_4 : cost_for_prime_entail_wit_3_65_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_65_split_goal_5 : cost_for_prime_entail_wit_3_65_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_cutfresh_lt_inf__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_65 : cost_for_prime_entail_wit_3_65.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_65_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_65_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_65_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_65_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_65_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_66_split_goal_1 : cost_for_prime_entail_wit_3_66_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  assert (Hce : cost = ElemCost b_pre p_pre (Znth i values 0)) by
    (rewrite Hce0, Hvi; reflexivity).
  assert (Hm1 : Z.min keep cutAfterKeep = cutAfterKeep) by (apply Z.min_r; lia).
  assert (Hm2 : Z.min (Z.min cutFresh cutAfterKeep) after = cutFresh).
  { rewrite (Z.min_l cutFresh cutAfterKeep) by lia. apply Z.min_l. lia. }
  replace (cutAfterKeep + a_pre) with (Z.min keep cutAfterKeep + a_pre) by lia.
  replace (cutFresh + cost) with
    (Z.min (Z.min cutFresh cutAfterKeep) after + cost) by lia.
  apply (cfp_state_step__cfp_step_12 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption; try (unfold INF in *; lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_66_split_goal_2 : cost_for_prime_entail_wit_3_66_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_66_split_goal_3 : cost_for_prime_entail_wit_3_66_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_66_split_goal_4 : cost_for_prime_entail_wit_3_66_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_66_split_goal_5 : cost_for_prime_entail_wit_3_66_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_66_split_goal_6 : cost_for_prime_entail_wit_3_66_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : forall j0 : Z, 0 <= j0 /\ j0 < n_pre ->
            2 <= Znth j0 values 0 /\ Znth j0 values 0 <= 1000000000) by assumption.
  apply Hrange; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_66 : cost_for_prime_entail_wit_3_66.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_66_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_66_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_66_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_66_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_66_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_66_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_67_split_goal_1 : cost_for_prime_entail_wit_3_67_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  apply (cfp_state_step__cfp_step_09 values a_pre b_pre p_pre i
           keep cutFresh cutAfterKeep after cost (keep + cost)).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - assumption.
  - unfold INF; lia.
  - assumption.
  - unfold INF; lia.
  - unfold INF; lia.
  - lia.
  - lia.
  - lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - right; unfold INF; split; [lia | split; [reflexivity | lia]].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_67_split_goal_2 : cost_for_prime_entail_wit_3_67_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_67_split_goal_3 : cost_for_prime_entail_wit_3_67_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_67_split_goal_4 : cost_for_prime_entail_wit_3_67_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_67_split_goal_5 : cost_for_prime_entail_wit_3_67_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  specialize (Bk ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_67_split_goal_6 : cost_for_prime_entail_wit_3_67_split_goal_6.
Proof.
  LLM_pre_process ltac:(idtac).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_67 : cost_for_prime_entail_wit_3_67.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_67_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_67_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_67_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_67_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_67_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_67_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_68_split_goal_1 : cost_for_prime_entail_wit_3_68_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  destruct Hst as [_ [_ [Hcak _]]].
  assert (Hi0 : i = 0) by lia.
  rewrite Hi0 in Hcak.
  pose proof (cfp_cak_zero_inf__cfp_step_12 values a_pre b_pre p_pre
                cutAfterKeep Hcak) as Hinf.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_68_split_goal_2 : cost_for_prime_entail_wit_3_68_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_68_split_goal_3 : cost_for_prime_entail_wit_3_68_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_68_split_goal_4 : cost_for_prime_entail_wit_3_68_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : forall j0 : Z, 0 <= j0 /\ j0 < n_pre ->
            2 <= Znth j0 values 0 /\ Znth j0 values 0 <= 1000000000) by assumption.
  apply Hrange; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_68 : cost_for_prime_entail_wit_3_68.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_68_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_68_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_68_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_68_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_69_split_goal_1 : cost_for_prime_entail_wit_3_69_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH37 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_69_split_goal_2 : cost_for_prime_entail_wit_3_69_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH37 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_69_split_goal_3 : cost_for_prime_entail_wit_3_69_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH37 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_69_split_goal_4 : cost_for_prime_entail_wit_3_69_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH37 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_69_split_goal_5 : cost_for_prime_entail_wit_3_69_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH37 as [_ [_ [Hak _]]].
  pose proof (dpcutafterkeep_zero__cfp_step_10 _ _ _ _ _ Hak) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_69 : cost_for_prime_entail_wit_3_69.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_69_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_69_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_69_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_69_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_69_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_70_split_goal_1 : cost_for_prime_entail_wit_3_70_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_70_split_goal_2 : cost_for_prime_entail_wit_3_70_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_70_split_goal_3 : cost_for_prime_entail_wit_3_70_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_70_split_goal_4 : cost_for_prime_entail_wit_3_70_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_70 : cost_for_prime_entail_wit_3_70.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_70_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_70_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_70_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_70_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_71_split_goal_1 : cost_for_prime_entail_wit_3_71_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_71_split_goal_2 : cost_for_prime_entail_wit_3_71_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_71_split_goal_3 : cost_for_prime_entail_wit_3_71_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_71 : cost_for_prime_entail_wit_3_71.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_71_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_71_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_71_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_72_split_goal_1 : cost_for_prime_entail_wit_3_72_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_72_split_goal_2 : cost_for_prime_entail_wit_3_72_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_72_split_goal_3 : cost_for_prime_entail_wit_3_72_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_72_split_goal_4 : cost_for_prime_entail_wit_3_72_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_state_i0_absurd__cfp_step_09 _ _ _ _ _ _ _ _ _ H
                    ltac:(lia) ltac:(lia)) as HA
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_72 : cost_for_prime_entail_wit_3_72.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_72_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_72_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_72_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_72_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_73_split_goal_1 : cost_for_prime_entail_wit_3_73_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_73_split_goal_2 : cost_for_prime_entail_wit_3_73_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_73_split_goal_3 : cost_for_prime_entail_wit_3_73_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_73 : cost_for_prime_entail_wit_3_73.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_73_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_73_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_73_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_74_split_goal_1 : cost_for_prime_entail_wit_3_74_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_74_split_goal_2 : cost_for_prime_entail_wit_3_74_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_74_split_goal_3 : cost_for_prime_entail_wit_3_74_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_74 : cost_for_prime_entail_wit_3_74.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_74_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_74_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_74_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_75_split_goal_1 : cost_for_prime_entail_wit_3_75_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf,
    HE : ?cst = ElemCost _ _ _ |- _ =>
      apply (cfp_state_step__cfp_step_11 aa dd cc pp ii kk ff akak afaf cst _ _)
  end.
  2: { right. repeat split; first [reflexivity | unfold INF in *; lia]. }
  1: { right. split; [reflexivity | unfold INF in *; lia]. }
  all: try (unfold INF in *; lia).
  all: try assumption.
  all: match goal with
       | HE : _ = ElemCost _ _ _ |- _ => rewrite HE
       end;
       match goal with
       | Hv : _ = Znth _ _ 0 |- _ => rewrite Hv
       end;
       reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_75_split_goal_2 : cost_for_prime_entail_wit_3_75_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_75_split_goal_3 : cost_for_prime_entail_wit_3_75_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: repeat match goal with
              | H : _ /\ _ |- _ => destruct H
              end.
  all: match goal with
       | H : context[Znth _ _ 0] |- _ => apply H; lia
       end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_75 : cost_for_prime_entail_wit_3_75.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_75_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_75_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_75_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_76_split_goal_1 : cost_for_prime_entail_wit_3_76_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  apply (cfp_state_step__cfp_step_09 values a_pre b_pre p_pre i
           keep cutFresh cutAfterKeep after cost (4611686018427387904)).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - assumption.
  - unfold INF; lia.
  - assumption.
  - unfold INF; lia.
  - unfold INF; lia.
  - lia.
  - lia.
  - lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - unfold INF; lia.
  - left; unfold INF; split; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_76_split_goal_2 : cost_for_prime_entail_wit_3_76_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_76_split_goal_3 : cost_for_prime_entail_wit_3_76_split_goal_3.
Proof.
  LLM_pre_process ltac:(idtac).
  subst v.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST
  end.
  assert (HB := cfp_state_finite_bound__cfp_step_09 values a_pre b_pre p_pre i
                  keep cutFresh cutAfterKeep after
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HST).
  destruct HB as [Bk [Bf [Bc Ba]]].
  unfold INF in Bk, Bf, Bc, Ba.
  assert (Hcne : ElemCost b_pre p_pre (Znth i values 0) <> INF)
    by (unfold INF; lia).
  pose proof (elemcost_bound__cfp_step_09 b_pre p_pre (Znth i values 0)
                ltac:(lia) Hcne) as Be.
  specialize (Bf ltac:(lia)).
  specialize (Bc ltac:(lia)).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_76_split_goal_4 : cost_for_prime_entail_wit_3_76_split_goal_4.
Proof.
  LLM_pre_process ltac:(idtac).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_76 : cost_for_prime_entail_wit_3_76.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_76_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_76_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_76_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_76_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_77_split_goal_1 : cost_for_prime_entail_wit_3_77_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH36)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH25. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH25; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  apply (cfp_state_step__cfp_step_10 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption;
    try (intros; try (unfold INF in * ); lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_77_split_goal_2 : cost_for_prime_entail_wit_3_77_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH36)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH25. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH25; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_77_split_goal_3 : cost_for_prime_entail_wit_3_77_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH36)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH25. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH25; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_77_split_goal_4 : cost_for_prime_entail_wit_3_77_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH18; assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_77 : cost_for_prime_entail_wit_3_77.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_77_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_77_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_77_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_77_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_78_split_goal_1 : cost_for_prime_entail_wit_3_78_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [_ Haf]]].
  pose proof (dpafter_zero__cfp_step_10 _ _ _ _ _ Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_78_split_goal_2 : cost_for_prime_entail_wit_3_78_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [_ Haf]]].
  pose proof (dpafter_zero__cfp_step_10 _ _ _ _ _ Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_78_split_goal_3 : cost_for_prime_entail_wit_3_78_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [_ Haf]]].
  pose proof (dpafter_zero__cfp_step_10 _ _ _ _ _ Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_78_split_goal_4 : cost_for_prime_entail_wit_3_78_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi : i = 0) by lia. subst i.
  destruct PreH35 as [_ [_ [_ Haf]]].
  pose proof (dpafter_zero__cfp_step_10 _ _ _ _ _ Haf) as Hzz.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_78 : cost_for_prime_entail_wit_3_78.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_78_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_78_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_78_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_78_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_79_split_goal_1 : cost_for_prime_entail_wit_3_79_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf,
    HE : ?cst = ElemCost _ _ _ |- _ =>
      apply (cfp_state_step__cfp_step_11 aa dd cc pp ii kk ff akak afaf cst _ _)
  end.
  2: { left. split; [reflexivity | left; lia]. }
  1: { left. split; [reflexivity | split; unfold INF in *; lia]. }
  all: try (unfold INF in *; lia).
  all: try assumption.
  all: match goal with
       | HE : _ = ElemCost _ _ _ |- _ => rewrite HE
       end;
       match goal with
       | Hv : _ = Znth _ _ 0 |- _ => rewrite Hv
       end;
       reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_79_split_goal_2 : cost_for_prime_entail_wit_3_79_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_79_split_goal_3 : cost_for_prime_entail_wit_3_79_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_79_split_goal_4 : cost_for_prime_entail_wit_3_79_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_79_split_goal_5 : cost_for_prime_entail_wit_3_79_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: repeat match goal with
              | H : _ /\ _ |- _ => destruct H
              end.
  all: match goal with
       | H : context[Znth _ _ 0] |- _ => apply H; lia
       end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_79 : cost_for_prime_entail_wit_3_79.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_79_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_79_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_79_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_79_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_79_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_80_split_goal_1 : cost_for_prime_entail_wit_3_80_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  assert (Hce : cost = ElemCost b_pre p_pre (Znth i values 0)) by
    (rewrite Hce0, Hvi; reflexivity).
  assert (Hm1 : Z.min keep cutAfterKeep = keep) by (apply Z.min_l; lia).
  assert (Hm2 : Z.min (Z.min cutFresh cutAfterKeep) after = cutFresh).
  { rewrite (Z.min_l cutFresh cutAfterKeep) by lia. apply Z.min_l. lia. }
  replace (keep + a_pre) with (Z.min keep cutAfterKeep + a_pre) by lia.
  replace (cutFresh + cost) with
    (Z.min (Z.min cutFresh cutAfterKeep) after + cost) by lia.
  apply (cfp_state_step__cfp_step_12 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption; try (unfold INF in *; lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_80_split_goal_2 : cost_for_prime_entail_wit_3_80_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_80_split_goal_3 : cost_for_prime_entail_wit_3_80_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_80_split_goal_4 : cost_for_prime_entail_wit_3_80_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_80_split_goal_5 : cost_for_prime_entail_wit_3_80_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_80_split_goal_6 : cost_for_prime_entail_wit_3_80_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : forall j0 : Z, 0 <= j0 /\ j0 < n_pre ->
            2 <= Znth j0 values 0 /\ Znth j0 values 0 <= 1000000000) by assumption.
  apply Hrange; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_80 : cost_for_prime_entail_wit_3_80.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_80_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_80_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_80_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_80_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_80_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_80_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_81_split_goal_1 : cost_for_prime_entail_wit_3_81_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH38 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_81_split_goal_2 : cost_for_prime_entail_wit_3_81_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH38 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_81_split_goal_3 : cost_for_prime_entail_wit_3_81_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH38 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_81_split_goal_4 : cost_for_prime_entail_wit_3_81_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH38 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_81_split_goal_5 : cost_for_prime_entail_wit_3_81_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  destruct PreH38 as [_ [Hf _]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf
     (dpcutfresh_mem__cfp_step_10 values a_pre b_pre p_pre i ltac:(lia) ltac:(lia))) as Hzz.
  assert (Hprod : i * a_pre <= 1000000000000000) by nia.
  unfold INF in Hzz. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_81 : cost_for_prime_entail_wit_3_81.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_81_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_81_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_81_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_81_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_81_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_82_split_goal_1 : cost_for_prime_entail_wit_3_82_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  assert (Hce : cost = ElemCost b_pre p_pre (Znth i values 0)) by
    (rewrite Hce0, Hvi; reflexivity).
  assert (Hm1 : Z.min keep cutAfterKeep = keep) by (apply Z.min_l; lia).
  assert (Hm2 : Z.min (Z.min cutFresh cutAfterKeep) after = cutFresh).
  { rewrite (Z.min_l cutFresh cutAfterKeep) by lia. apply Z.min_l. lia. }
  replace (keep + a_pre) with (Z.min keep cutAfterKeep + a_pre) by lia.
  replace (cutFresh + cost) with
    (Z.min (Z.min cutFresh cutAfterKeep) after + cost) by lia.
  apply (cfp_state_step__cfp_step_12 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption; try (unfold INF in *; lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_82_split_goal_2 : cost_for_prime_entail_wit_3_82_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_82_split_goal_3 : cost_for_prime_entail_wit_3_82_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_82_split_goal_4 : cost_for_prime_entail_wit_3_82_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_82_split_goal_5 : cost_for_prime_entail_wit_3_82_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hst : CostForPrimeState values a_pre b_pre p_pre i keep cutFresh
                  cutAfterKeep after) by assumption.
  assert (Hce0 : cost = ElemCost b_pre p_pre v) by assumption.
  assert (Hvi : v = Znth i values 0) by assumption.
  assert (Hcne : ElemCost b_pre p_pre v <> INF) by (unfold INF; lia).
  assert (Hcb : cost <= b_pre) by
    (rewrite Hce0; apply elemcost_le_change__cfp_step_12; [lia | exact Hcne]).
  pose proof (cfp_state_finite_bound__cfp_step_12 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst)
    as [Bk [Bf [Bc Bb]]].
  try (assert (Xk : 0 <= keep <= 2000000000000000)
         by (apply Bk; unfold INF; lia));
  try (assert (Xf : 0 <= cutFresh <= 2000000000000000)
         by (apply Bf; unfold INF; lia));
  try (assert (Xc : 0 <= cutAfterKeep <= 2000000000000000)
         by (apply Bc; unfold INF; lia));
  try (assert (Xb : 0 <= after <= 2000000000000000)
         by (apply Bb; unfold INF; lia));
  try (unfold INF in *); lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_82_split_goal_6 : cost_for_prime_entail_wit_3_82_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : forall j0 : Z, 0 <= j0 /\ j0 < n_pre ->
            2 <= Znth j0 values 0 /\ Znth j0 values 0 <= 1000000000) by assumption.
  apply Hrange; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_82 : cost_for_prime_entail_wit_3_82.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_82_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_82_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_82_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_82_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_82_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_82_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_83_split_goal_1 : cost_for_prime_entail_wit_3_83_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH38)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH27. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH27; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbk ltac:(unfold INF; lia)).
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hba ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  apply (cfp_state_step__cfp_step_10 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after cost);
    try assumption;
    try (intros; try (unfold INF in * ); lia).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_83_split_goal_2 : cost_for_prime_entail_wit_3_83_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH38)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH27. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH27; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbk ltac:(unfold INF; lia)).
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hba ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_83_split_goal_3 : cost_for_prime_entail_wit_3_83_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH38)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH27. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH27; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbk ltac:(unfold INF; lia)).
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hba ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_83_split_goal_4 : cost_for_prime_entail_wit_3_83_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH38)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH27. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH27; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbk ltac:(unfold INF; lia)).
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hba ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_83_split_goal_5 : cost_for_prime_entail_wit_3_83_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst v.
  assert (Hz : Zlength values = n_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_10 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH38)
    as [Hbk [Hbf [Hba Hbaf]]].
  rewrite Hz in Hbk, Hbf, Hba, Hbaf.
  assert (Hbig : n_pre * a_pre + 2 * (n_pre * b_pre) <= 3000000000000000) by nia.
  assert (Hcost : 0 <= cost <= b_pre).
  { rewrite PreH27. apply elemcost_range__cfp_step_10;
      [lia | rewrite <- PreH27; unfold INF; lia]. }
  assert (Hid : i * a_pre <= 1000000000000000) by nia.
  assert (Hid1 : (i + 1) * a_pre <= 1000000000000000) by nia.
  specialize (Hbk ltac:(unfold INF; lia)).
  specialize (Hbf ltac:(unfold INF; lia)).
  specialize (Hba ltac:(unfold INF; lia)).
  specialize (Hbaf ltac:(unfold INF; lia)).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_83_split_goal_6 : cost_for_prime_entail_wit_3_83_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH20; assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_83 : cost_for_prime_entail_wit_3_83.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_83_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_83_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_83_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_83_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_83_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_83_split_goal_6.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_84_split_goal_1 : cost_for_prime_entail_wit_3_84_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_84_split_goal_2 : cost_for_prime_entail_wit_3_84_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_84_split_goal_3 : cost_for_prime_entail_wit_3_84_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_84_split_goal_4 : cost_for_prime_entail_wit_3_84_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_84_split_goal_5 : cost_for_prime_entail_wit_3_84_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_84 : cost_for_prime_entail_wit_3_84.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_84_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_84_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_84_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_84_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_84_split_goal_5.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_85_split_goal_1 : cost_for_prime_entail_wit_3_85_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_85_split_goal_2 : cost_for_prime_entail_wit_3_85_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_85_split_goal_3 : cost_for_prime_entail_wit_3_85_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_85_split_goal_4 : cost_for_prime_entail_wit_3_85_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_85_split_goal_5 : cost_for_prime_entail_wit_3_85_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_85 : cost_for_prime_entail_wit_3_85.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_85_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_85_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_85_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_85_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_85_split_goal_5.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_86_split_goal_1 : cost_for_prime_entail_wit_3_86_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_86_split_goal_2 : cost_for_prime_entail_wit_3_86_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_86_split_goal_3 : cost_for_prime_entail_wit_3_86_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_86_split_goal_4 : cost_for_prime_entail_wit_3_86_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_86 : cost_for_prime_entail_wit_3_86.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_86_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_86_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_86_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_86_split_goal_4.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_87_split_goal_1 : cost_for_prime_entail_wit_3_87_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_87_split_goal_2 : cost_for_prime_entail_wit_3_87_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_87_split_goal_3 : cost_for_prime_entail_wit_3_87_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_87_split_goal_4 : cost_for_prime_entail_wit_3_87_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exfalso.
  all: match goal with
       | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
           pose proof (cfp_cutafterkeep_zero_contra__cfp_step_11
                         _ _ _ _ _ _ _ _ _ H ltac:(lia)) as Hcak
       end.
  all: unfold INF in Hcak; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_87 : cost_for_prime_entail_wit_3_87.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_87_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_87_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_87_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_87_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_88_split_goal_1 : cost_for_prime_entail_wit_3_88_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_88_split_goal_2 : cost_for_prime_entail_wit_3_88_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_88_split_goal_3 : cost_for_prime_entail_wit_3_88_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_88_split_goal_4 : cost_for_prime_entail_wit_3_88_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_88 : cost_for_prime_entail_wit_3_88.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_88_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_88_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_88_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_88_split_goal_4.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_89_split_goal_1 : cost_for_prime_entail_wit_3_89_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_89_split_goal_2 : cost_for_prime_entail_wit_3_89_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_89_split_goal_3 : cost_for_prime_entail_wit_3_89_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH18 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_89 : cost_for_prime_entail_wit_3_89.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_89_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_89_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_89_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_90_split_goal_1 : cost_for_prime_entail_wit_3_90_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_90_split_goal_2 : cost_for_prime_entail_wit_3_90_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (cfp_cutfresh_finite__cfp_step_07 _ _ _ _ _ _ _ _ _ HS
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hst
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_90_split_goal_3 : cost_for_prime_entail_wit_3_90_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH19 j H).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_90 : cost_for_prime_entail_wit_3_90.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_90_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_90_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_90_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_91_split_goal_1 : cost_for_prime_entail_wit_3_91_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf,
    HE : ?cst = ElemCost _ _ _ |- _ =>
      apply (cfp_state_step__cfp_step_11 aa dd cc pp ii kk ff akak afaf cst _ _)
  end.
  2: { left. split; [reflexivity | right; split; unfold INF in *; lia]. }
  1: { right. split; [reflexivity | unfold INF in *; lia]. }
  all: try (unfold INF in *; lia).
  all: try assumption.
  all: match goal with
       | HE : _ = ElemCost _ _ _ |- _ => rewrite HE
       end;
       match goal with
       | Hv : _ = Znth _ _ 0 |- _ => rewrite Hv
       end;
       reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_91_split_goal_2 : cost_for_prime_entail_wit_3_91_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_91_split_goal_3 : cost_for_prime_entail_wit_3_91_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | HS : CostForPrimeState ?aa ?dd ?cc ?pp ?ii ?kk ?ff ?akak ?afaf |- _ =>
      pose proof (cfp_state_finite_bound__cfp_step_11 aa dd cc pp ii kk ff akak afaf
                    ltac:(lia) ltac:(lia) ltac:(lia) HS) as [Hbk [Hbf [Hbc Hba]]]
  end.
  match goal with
  | HE : _ = ElemCost ?ch ?pp ?xx |- _ =>
      pose proof (ElemCost_bound__cfp_step_11 ch pp xx ltac:(lia)
                    ltac:(rewrite <- HE; unfold INF; lia)) as Hce;
      rewrite <- HE in Hce
  end.
  try (specialize (Hbk ltac:(unfold INF; lia))).
  try (specialize (Hbf ltac:(unfold INF; lia))).
  try (specialize (Hbc ltac:(unfold INF; lia))).
  try (specialize (Hba ltac:(unfold INF; lia))).
  unfold INF in *. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_91_split_goal_4 : cost_for_prime_entail_wit_3_91_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: repeat match goal with
              | H : _ /\ _ |- _ => destruct H
              end.
  all: match goal with
       | H : context[Znth _ _ 0] |- _ => apply H; lia
       end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_91 : cost_for_prime_entail_wit_3_91.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_91_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_91_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_91_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_91_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_92_split_goal_1 : cost_for_prime_entail_wit_3_92_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_92_split_goal_2 : cost_for_prime_entail_wit_3_92_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_92_split_goal_3 : cost_for_prime_entail_wit_3_92_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_92_split_goal_4 : cost_for_prime_entail_wit_3_92_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i ?k ?cf ?ck ?af |- _ =>
      pose proof (cfp_state_cutfresh_bound__cfp_step_08 a d c p i k cf ck af
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H)
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_92 : cost_for_prime_entail_wit_3_92.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_92_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_92_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_92_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_92_split_goal_4.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_93_split_goal_1 : cost_for_prime_entail_wit_3_93_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_93_split_goal_2 : cost_for_prime_entail_wit_3_93_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH18; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_93 : cost_for_prime_entail_wit_3_93.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_93_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_93_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_94_split_goal_1 : cost_for_prime_entail_wit_3_94_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_94_split_goal_2 : cost_for_prime_entail_wit_3_94_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH17; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_94 : cost_for_prime_entail_wit_3_94.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_94_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_94_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_95_split_goal_1 : cost_for_prime_entail_wit_3_95_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH36)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_95_split_goal_2 : cost_for_prime_entail_wit_3_95_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH36)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_95_split_goal_3 : cost_for_prime_entail_wit_3_95_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH18. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_95 : cost_for_prime_entail_wit_3_95.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_95_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_95_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_95_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_96_split_goal_1 : cost_for_prime_entail_wit_3_96_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_96_split_goal_2 : cost_for_prime_entail_wit_3_96_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_96_split_goal_3 : cost_for_prime_entail_wit_3_96_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_96_split_goal_4 : cost_for_prime_entail_wit_3_96_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_96 : cost_for_prime_entail_wit_3_96.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_96_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_96_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_96_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_96_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_97_split_goal_1 : cost_for_prime_entail_wit_3_97_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cfp_state_cutfresh_le__cfp_step_02 values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) PreH35) as Hcf__.
  exfalso.
  assert (Hm__ : i * a_pre <= 1000000 * 1000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_97_split_goal_2 : cost_for_prime_entail_wit_3_97_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cfp_state_cutfresh_le__cfp_step_02 values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) PreH35) as Hcf__.
  exfalso.
  assert (Hm__ : i * a_pre <= 1000000 * 1000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_97_split_goal_3 : cost_for_prime_entail_wit_3_97_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH17. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_97 : cost_for_prime_entail_wit_3_97.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_97_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_97_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_97_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_98_split_goal_1 : cost_for_prime_entail_wit_3_98_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  assert (HEC : ElemCost b_pre p_pre (Znth i values 0) = INF).
  { unfold INF.
    match goal with H : v = Znth i values 0 |- _ => rewrite <- H end.
    match goal with H : cost = ElemCost b_pre p_pre v |- _ => rewrite <- H end.
    assumption. }
  apply (cfp_state_step__cfp_step_03 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after); unfold INF in *; solve [assumption | lia].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_98_split_goal_2 : cost_for_prime_entail_wit_3_98_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_98_split_goal_3 : cost_for_prime_entail_wit_3_98_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_98_split_goal_4 : cost_for_prime_entail_wit_3_98_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_98 : cost_for_prime_entail_wit_3_98.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_98_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_98_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_98_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_98_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_99_split_goal_1 : cost_for_prime_entail_wit_3_99_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  assert (HEC : ElemCost b_pre p_pre (Znth i values 0) = INF).
  { unfold INF.
    match goal with H : v = Znth i values 0 |- _ => rewrite <- H end.
    match goal with H : cost = ElemCost b_pre p_pre v |- _ => rewrite <- H end.
    assumption. }
  apply (cfp_state_step__cfp_step_03 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after); unfold INF in *; solve [assumption | lia].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_99_split_goal_2 : cost_for_prime_entail_wit_3_99_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_99_split_goal_3 : cost_for_prime_entail_wit_3_99_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_99_split_goal_4 : cost_for_prime_entail_wit_3_99_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_99 : cost_for_prime_entail_wit_3_99.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_99_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_99_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_99_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_99_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_100_split_goal_1 : cost_for_prime_entail_wit_3_100_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_100_split_goal_2 : cost_for_prime_entail_wit_3_100_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_100 : cost_for_prime_entail_wit_3_100.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_100_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_100_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_101_split_goal_1 : cost_for_prime_entail_wit_3_101_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_101_split_goal_2 : cost_for_prime_entail_wit_3_101_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_101_split_goal_3 : cost_for_prime_entail_wit_3_101_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_101 : cost_for_prime_entail_wit_3_101.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_101_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_101_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_101_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_102_split_goal_1 : cost_for_prime_entail_wit_3_102_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_102_split_goal_2 : cost_for_prime_entail_wit_3_102_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_102 : cost_for_prime_entail_wit_3_102.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_102_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_102_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_103_split_goal_1 : cost_for_prime_entail_wit_3_103_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_103_split_goal_2 : cost_for_prime_entail_wit_3_103_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_103 : cost_for_prime_entail_wit_3_103.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_103_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_103_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_104_split_goal_1 : cost_for_prime_entail_wit_3_104_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_104_split_goal_2 : cost_for_prime_entail_wit_3_104_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_104_split_goal_3 : cost_for_prime_entail_wit_3_104_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_104 : cost_for_prime_entail_wit_3_104.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_104_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_104_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_104_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_105_split_goal_1 : cost_for_prime_entail_wit_3_105_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hi0 : i = 0) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hi0 in H;
    pose proof (cfp_state_zero_cak_inf__cfp_step_03 _ _ _ _ _ _ _ _ H) as HZ
  end.
  unfold INF in HZ. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_105_split_goal_2 : cost_for_prime_entail_wit_3_105_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_105 : cost_for_prime_entail_wit_3_105.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_105_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_105_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_106_split_goal_1 : cost_for_prime_entail_wit_3_106_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [_ [HF _]] end.
  assert (Hib : 0 <= i <= Zlength values) by lia.
  assert (Hb : i * a_pre <= 1000000000000000) by nia.
  assert (HV : DPValue (DPCutFresh values a_pre b_pre p_pre i) (i * a_pre)).
  { apply dpcutfresh_value__cfp_step_03; [lia | unfold INF; lia]. }
  pose proof (dpvalue_unique__cfp_step_03 _ _ _ HF HV) as HU.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_106_split_goal_2 : cost_for_prime_entail_wit_3_106_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_106 : cost_for_prime_entail_wit_3_106.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_106_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_106_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_107_split_goal_1 : cost_for_prime_entail_wit_3_107_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  assert (HEC : ElemCost b_pre p_pre (Znth i values 0) = INF).
  { unfold INF.
    match goal with H : v = Znth i values 0 |- _ => rewrite <- H end.
    match goal with H : cost = ElemCost b_pre p_pre v |- _ => rewrite <- H end.
    assumption. }
  apply (cfp_state_step__cfp_step_03 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after); unfold INF in *; solve [assumption | lia].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_107_split_goal_2 : cost_for_prime_entail_wit_3_107_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_107 : cost_for_prime_entail_wit_3_107.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_107_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_107_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_108_split_goal_1 : cost_for_prime_entail_wit_3_108_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  assert (HEC : ElemCost b_pre p_pre (Znth i values 0) = INF).
  { unfold INF.
    match goal with H : v = Znth i values 0 |- _ => rewrite <- H end.
    match goal with H : cost = ElemCost b_pre p_pre v |- _ => rewrite <- H end.
    assumption. }
  apply (cfp_state_step__cfp_step_03 values a_pre b_pre p_pre i keep cutFresh
           cutAfterKeep after); unfold INF in *; solve [assumption | lia].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_108_split_goal_2 : cost_for_prime_entail_wit_3_108_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => rename H into HST end.
  assert (Hdel : 0 <= a_pre) by lia.
  assert (Hch : 0 <= b_pre) by lia.
  pose proof (cfp_state_finite_bound__cfp_step_03 values a_pre b_pre p_pre i
                keep cutFresh cutAfterKeep after Hdel Hch HST) as HB.
  destruct HB as [HBk [HBf [HBa HBo]]].
  assert (Hb1 : Zlength values * a_pre <= 1000000000000000) by nia.
  assert (Hb2 : Zlength values * b_pre <= 1000000000000000) by nia.
  assert (Hcfne : cutFresh <> INF) by (unfold INF; assumption).
  assert (Hakne : cutAfterKeep <> INF) by (unfold INF; assumption).
  specialize (HBf Hcfne). specialize (HBa Hakne).
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_108_split_goal_3 : cost_for_prime_entail_wit_3_108_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall jj : Z, 0 <= jj < n_pre -> _ |- _ => apply H
  end.
  assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_108 : cost_for_prime_entail_wit_3_108.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_108_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_108_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_108_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_109_split_goal_1 : cost_for_prime_entail_wit_3_109_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [Hk [Hcf [Hcak Haf]]]
  end.
  assert (HEC : ElemCost b_pre p_pre (Znth i values 0) = INF).
  { unfold INF. rewrite <- PreH19, <- PreH22. exact PreH1. }
  assert (Hcfv : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  destruct Hcfv as [Hcfv _].
  rewrite PreH4 in Hk. rewrite PreH3 in Hcak.
  unfold CostForPrimeState.
  split; [| split; [| split]].
  - apply (dpkeep_step_inf__cfp_step_01 values a_pre b_pre p_pre i);
      [ lia | lia | lia | lia | unfold INF; lia | exact HEC ].
  - replace (cutFresh + a_pre) with ((i + 1) * a_pre) by (rewrite Hcfv; ring).
    apply cutfresh_intro__cfp_step_01;
      [ lia
      | lia
      | assert ((i + 1) * a_pre <= 1000001 * 1000000000)
          by (apply Z.mul_le_mono_nonneg; lia);
        unfold INF; lia ].
  - apply (dpcutafterkeep_step_inf__cfp_step_01 values a_pre b_pre p_pre i);
      [ lia | lia | lia | exact Hk | exact Hcak ].
  - apply (dpafter_step_inf__cfp_step_01 values a_pre b_pre p_pre i);
      [ lia | lia | lia | lia | unfold INF; lia | exact HEC ].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_109_split_goal_2 : cost_for_prime_entail_wit_3_109_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_109_split_goal_3 : cost_for_prime_entail_wit_3_109_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH15; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_109 : cost_for_prime_entail_wit_3_109.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_109_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_109_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_109_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_110_split_goal_1 : cost_for_prime_entail_wit_3_110_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_110_split_goal_2 : cost_for_prime_entail_wit_3_110_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH15; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_110 : cost_for_prime_entail_wit_3_110.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_110_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_110_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_111_split_goal_1 : cost_for_prime_entail_wit_3_111_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_111_split_goal_2 : cost_for_prime_entail_wit_3_111_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH15; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_111 : cost_for_prime_entail_wit_3_111.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_111_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_111_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_112_split_goal_1 : cost_for_prime_entail_wit_3_112_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH33) as [_ [Hcf0__ _]].
  assert (HcfE__ : cutFresh = 0) by lia. subst cutFresh.
  assert (Hlen__ : 1 <= Zlength values) by lia.
  assert (Hx__ : sublist 0 1 values = cons (Znth 0 values 0) nil)
    by (apply sublist_first__cfp_step_02; lia).
  assert (Hemp0__ : sublist 0 0 values = nil)
    by (apply sublist_empty__cfp_step_02; lia).
  assert (Hemp1__ : sublist 1 1 values = nil)
    by (apply sublist_empty__cfp_step_02; lia).
  assert (Hec__ : ElemCost b_pre p_pre (Znth 0 values 0) = INF).
  { rewrite <- PreH19. rewrite <- PreH22. unfold INF. lia. }
  assert (Hchne__ : b_pre <> INF) by (unfold INF; lia).
  assert (HkeptA__ : sublist 0 1 values ++ sublist 1 1 values = cons (Znth 0 values 0) nil).
  { rewrite Hx__, Hemp1__. reflexivity. }
  assert (HkeptB__ : sublist 0 0 values ++ sublist 0 1 values = cons (Znth 0 values 0) nil).
  { rewrite Hx__, Hemp0__. reflexivity. }
  replace (0 + 1) with 1 by lia.
  unfold CostForPrimeState. split; [| split; [| split]].
  - apply dpvalue_of_empty__cfp_step_02. intros c Hc__. unfold DPKeep in Hc__.
    exact (plan_kept_one_infeasible__cfp_step_02 values a_pre b_pre p_pre 1 1 1 c
             (Znth 0 values 0) PreH16 Hchne__ Hec__ HkeptA__ Hc__).
  - apply dpvalue_intro__cfp_step_02.
    + replace (0 + a_pre) with (1 * a_pre) by lia.
      unfold DPCutFresh. apply plan_cut_all__cfp_step_02. lia.
    + intros c Hc__. unfold DPCutFresh in Hc__.
      assert (Hnil__ : sublist 0 0 values ++ sublist 1 1 values = nil).
      { rewrite Hemp0__, Hemp1__. reflexivity. }
      pose proof (plan_kept_nil_cost__cfp_step_02 _ _ _ _ _ _ _ _ Hnil__ Hc__). lia.
    + unfold INF. lia.
  - apply dpvalue_of_empty__cfp_step_02. intros c Hc__. unfold DPCutAfterKeep in Hc__.
    destruct Hc__ as [l [Hl1__ [Hl2__ _]]]. lia.
  - apply dpvalue_of_empty__cfp_step_02. intros c Hc__. unfold DPAfter in Hc__.
    destruct Hc__ as [l [r [Hr__ HP__]]].
    assert (Hlr__ : l = 0 /\ r = 0).
    { destruct HP__ as [A__ [B__ [C__ _]]]. lia. }
    destruct Hlr__ as [Hl0__ Hr0__]. subst l. subst r.
    exact (plan_kept_one_infeasible__cfp_step_02 values a_pre b_pre p_pre 1 0 0 c
             (Znth 0 values 0) PreH16 Hchne__ Hec__ HkeptB__ HP__).
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_112_split_goal_2 : cost_for_prime_entail_wit_3_112_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH33) as [_ [Hcf0__ _]].
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_112_split_goal_3 : cost_for_prime_entail_wit_3_112_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH15. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_112 : cost_for_prime_entail_wit_3_112.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_112_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_112_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_112_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_113_split_goal_1 : cost_for_prime_entail_wit_3_113_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_113_split_goal_2 : cost_for_prime_entail_wit_3_113_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH14; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_113 : cost_for_prime_entail_wit_3_113.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_113_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_113_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_114_split_goal_1 : cost_for_prime_entail_wit_3_114_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH32)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_114_split_goal_2 : cost_for_prime_entail_wit_3_114_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH32)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_114_split_goal_3 : cost_for_prime_entail_wit_3_114_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH14. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_114 : cost_for_prime_entail_wit_3_114.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_114_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_114_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_114_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_115_split_goal_1 : cost_for_prime_entail_wit_3_115_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_115_split_goal_2 : cost_for_prime_entail_wit_3_115_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_115_split_goal_3 : cost_for_prime_entail_wit_3_115_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_115_split_goal_4 : cost_for_prime_entail_wit_3_115_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_115 : cost_for_prime_entail_wit_3_115.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_115_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_115_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_115_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_115_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_116_split_goal_1 : cost_for_prime_entail_wit_3_116_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_116_split_goal_2 : cost_for_prime_entail_wit_3_116_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_116_split_goal_3 : cost_for_prime_entail_wit_3_116_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_116 : cost_for_prime_entail_wit_3_116.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_116_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_116_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_116_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_117_split_goal_1 : cost_for_prime_entail_wit_3_117_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_117_split_goal_2 : cost_for_prime_entail_wit_3_117_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_117_split_goal_3 : cost_for_prime_entail_wit_3_117_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_117 : cost_for_prime_entail_wit_3_117.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_117_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_117_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_117_split_goal_3.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_118_split_goal_1 : cost_for_prime_entail_wit_3_118_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_118_split_goal_2 : cost_for_prime_entail_wit_3_118_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_118_split_goal_3 : cost_for_prime_entail_wit_3_118_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_118_split_goal_4 : cost_for_prime_entail_wit_3_118_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_118 : cost_for_prime_entail_wit_3_118.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_118_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_118_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_118_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_118_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_119_split_goal_1 : cost_for_prime_entail_wit_3_119_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HST end.
  destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
              cutAfterKeep after ltac:(lia) ltac:(lia) HST)
    as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]].
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    apply (cfp_state_step__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh cutAfterKeep
             after cost (Z.min keep cutAfterKeep)
             (Z.min cutFresh (Z.min cutAfterKeep after)));
    unfold INF in *; try assumption; try lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_119_split_goal_2 : cost_for_prime_entail_wit_3_119_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_119_split_goal_3 : cost_for_prime_entail_wit_3_119_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst v.
  assert (HZ : Zlength values = n_pre) by lia.
  match goal with H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cfp_state_finite_bound__cfp_step_04 values a_pre b_pre p_pre i keep cutFresh
                cutAfterKeep after ltac:(lia) ltac:(lia) H)
      as [[Hk0 Hk1] [[Hf0 Hf1] [[Hc0 Hc1] [Ha0 Ha1]]]] end.
  assert (HB : Zlength values * a_pre + 2 * (Zlength values * b_pre) <= 3000000000000000)
    by nia.
  destruct (elemcost_cases__cfp_step_04 b_pre p_pre (Znth i values 0)) as [Hec | [Hec | Hec]];
    unfold INF in *; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_119_split_goal_4 : cost_for_prime_entail_wit_3_119_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : forall _ : Z, _ |- _ => apply H; lia end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_119 : cost_for_prime_entail_wit_3_119.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_119_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_119_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_119_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_119_split_goal_4.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_120_split_goal_1 : cost_for_prime_entail_wit_3_120_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH33)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_120_split_goal_2 : cost_for_prime_entail_wit_3_120_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH33)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_120_split_goal_3 : cost_for_prime_entail_wit_3_120_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH15. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_120 : cost_for_prime_entail_wit_3_120.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_120_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_120_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_120_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_121_split_goal_1 : cost_for_prime_entail_wit_3_121_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH33)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_121_split_goal_2 : cost_for_prime_entail_wit_3_121_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH33)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_121_split_goal_3 : cost_for_prime_entail_wit_3_121_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH15. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_121 : cost_for_prime_entail_wit_3_121.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_121_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_121_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_121_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_122_split_goal_1 : cost_for_prime_entail_wit_3_122_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_122_split_goal_2 : cost_for_prime_entail_wit_3_122_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH15; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_122 : cost_for_prime_entail_wit_3_122.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_122_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_122_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_123_split_goal_1 : cost_for_prime_entail_wit_3_123_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH34)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_123_split_goal_2 : cost_for_prime_entail_wit_3_123_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH34)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_123_split_goal_3 : cost_for_prime_entail_wit_3_123_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH16. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_123 : cost_for_prime_entail_wit_3_123.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_123_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_123_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_123_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_124_split_goal_1 : cost_for_prime_entail_wit_3_124_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH34)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_124_split_goal_2 : cost_for_prime_entail_wit_3_124_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi__ : i = 0) by lia. subst i.
  pose proof (cfp_state_zero__cfp_step_02 _ _ _ _ _ _ _ _ PreH34)
    as [Hk__ [Hcf__ [Hca__ Haf__]]].
  unfold INF in Hca__, Haf__.
  exfalso. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_124_split_goal_3 : cost_for_prime_entail_wit_3_124_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH16. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_124 : cost_for_prime_entail_wit_3_124.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_124_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_124_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_124_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_125_split_goal_1 : cost_for_prime_entail_wit_3_125_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_125_split_goal_2 : cost_for_prime_entail_wit_3_125_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH16; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_125 : cost_for_prime_entail_wit_3_125.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_125_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_125_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_126_split_goal_1 : cost_for_prime_entail_wit_3_126_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ [Hcf _]]
  end.
  assert (Hb : cutFresh = i * a_pre /\ cutFresh <= 1000000000000000).
  { apply (cutfresh_bound__cfp_step_01 values a_pre b_pre p_pre i cutFresh);
      [ lia | lia | lia | lia | lia | exact Hcf ]. }
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_126_split_goal_2 : cost_for_prime_entail_wit_3_126_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; apply PreH16; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_126 : cost_for_prime_entail_wit_3_126.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_126_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_126_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_127_split_goal_1 : cost_for_prime_entail_wit_3_127_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cfp_state_finite_bound__cfp_step_02 values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH34)
    as [_ [_ [Hca__ _]]].
  specialize (Hca__ PreH4).
  rewrite <- PreH15 in Hca__.
  exfalso.
  assert (H1__ : n_pre * a_pre <= 1000000 * 1000000000) by nia.
  assert (H2__ : n_pre * b_pre <= 1000000 * 1000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_127_split_goal_2 : cost_for_prime_entail_wit_3_127_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cfp_state_finite_bound__cfp_step_02 values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH34)
    as [_ [_ [Hca__ _]]].
  specialize (Hca__ PreH4).
  rewrite <- PreH15 in Hca__.
  exfalso.
  assert (H1__ : n_pre * a_pre <= 1000000 * 1000000000) by nia.
  assert (H2__ : n_pre * b_pre <= 1000000 * 1000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_127_split_goal_3 : cost_for_prime_entail_wit_3_127_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH16. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_127 : cost_for_prime_entail_wit_3_127.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_127_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_127_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_127_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_128_split_goal_1 : cost_for_prime_entail_wit_3_128_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cfp_state_finite_bound__cfp_step_02 values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH34)
    as [_ [_ [Hca__ _]]].
  specialize (Hca__ PreH4).
  rewrite <- PreH15 in Hca__.
  exfalso.
  assert (H1__ : n_pre * a_pre <= 1000000 * 1000000000) by nia.
  assert (H2__ : n_pre * b_pre <= 1000000 * 1000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_128_split_goal_2 : cost_for_prime_entail_wit_3_128_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cfp_state_finite_bound__cfp_step_02 values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) ltac:(lia) PreH34)
    as [_ [_ [Hca__ _]]].
  specialize (Hca__ PreH4).
  rewrite <- PreH15 in Hca__.
  exfalso.
  assert (H1__ : n_pre * a_pre <= 1000000 * 1000000000) by nia.
  assert (H2__ : n_pre * b_pre <= 1000000 * 1000000000) by nia.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_128_split_goal_3 : cost_for_prime_entail_wit_3_128_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH16. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_128 : cost_for_prime_entail_wit_3_128.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_128_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_128_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_128_split_goal_3.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_4_1_split_goal_1 : cost_for_prime_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with cutAfterKeep in Hcfp by lia.
  exact Hcfp.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_1_split_goal_2 : cost_for_prime_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with cutAfterKeep in Hcfp by lia.
  pose proof (cost_for_prime_bound__cfp_exit_min values a_pre b_pre p_pre cutAfterKeep
                ltac:(lia) ltac:(lia) ltac:(lia) Hcfp ltac:(unfold INF; lia)) as Hb.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_1 : cost_for_prime_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_4_1_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_2_split_goal_1 : cost_for_prime_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with cutAfterKeep in Hcfp by lia.
  exact Hcfp.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_2_split_goal_2 : cost_for_prime_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with cutAfterKeep in Hcfp by lia.
  pose proof (cost_for_prime_bound__cfp_exit_min values a_pre b_pre p_pre cutAfterKeep
                ltac:(lia) ltac:(lia) ltac:(lia) Hcfp ltac:(unfold INF; lia)) as Hb.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_2 : cost_for_prime_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_4_2_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_3_split_goal_1 : cost_for_prime_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with after in Hcfp by lia.
  exact Hcfp.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_3_split_goal_2 : cost_for_prime_entail_wit_4_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with after in Hcfp by lia.
  pose proof (cost_for_prime_bound__cfp_exit_min values a_pre b_pre p_pre after
                ltac:(lia) ltac:(lia) ltac:(lia) Hcfp ltac:(unfold INF; lia)) as Hb.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_3 : cost_for_prime_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_4_3_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_4_3_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_4 : cost_for_prime_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with keep in Hcfp by lia.
  destruct (Z.eq_dec keep 4611686018427387904) as [Heq | Hne].
  - Left.
    split_pure_spatial.
    + cancel (IntArray.full arr_pre n_pre values).
    + split_pures; dump_pre_spatial; first [ exact Hcfp | lia ].
  - assert (Hb : 0 <= keep <= 2000000000000000).
    { apply (cost_for_prime_bound__cfp_exit_min values a_pre b_pre p_pre keep
               ltac:(lia) ltac:(lia) ltac:(lia) Hcfp).
      unfold INF. lia. }
    Right.
    split_pure_spatial.
    + cancel (IntArray.full arr_pre n_pre values).
    + split_pures; dump_pre_spatial; first [ exact Hcfp | lia ].
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: apply candidate_coverage_init__solver_candidate_coverage.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: apply Zlength_nil.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: intros j Hj.
  all: apply PreH7.
  all: exact Hj.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply Int64Array.full_shape_to_seg_shape.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply candidate_coverage_extend__solver_candidate_coverage.
  all: assumption.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: rewrite Zlength_app.
  all: rewrite Zlength_app.
  all: lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply best_prefix_cost_empty__solver_candidate_coverage.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: assert (Hd : d = 2) by lia.
  all: subst d.
  all: exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply (candidate_coverage_Znth__solver_candidate_coverage _ _ _ _ _ PreH15).
  all: lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH9.
  all: lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in PreH2 by lia.
  eapply best_prefix_cost_step__solver_best_prefix.
  - lia.
  - exact PreH23.
  - exact PreH2.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in PreH2 by lia.
  eapply best_prefix_cost_step__solver_best_prefix.
  - lia.
  - exact PreH23.
  - exact PreH2.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in PreH2 by lia.
  eapply best_prefix_cost_step__solver_best_prefix.
  - lia.
  - exact PreH22.
  - exact PreH2.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (best_prefix_gives_spec__solver_spec_final values a_pre b_pre ps best).
  - lia.
  - lia.
  - lia.
  - intros j Hj. destruct (PreH11 j ltac:(lia)). lia.
  - intros j Hj. apply PreH17. lia.
  - rewrite <- PreH10. exact PreH18.
  - replace (Zlength ps) with i by lia. exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_app.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure_split_goal_1 : solver_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_6_pure_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (Int64Array.seg_to_seg_shape primes 0 nprime ps).
  sep_apply (Int64Array.seg_shape_merge_to_seg_shape primes 0 nprime 256); try lia.
  sep_apply (Int64Array.seg_shape_to_full_shape primes 0 256).
  rewrite Z.mul_0_l, Z.add_0_r.
  replace (256 - 0) with 256 by lia.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
Qed. 

