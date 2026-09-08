import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_goal
import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open super_piano_goal super_piano_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem cell_to_seg (p i value : Int) :
    ((p+i*sizeof(INT)) # Int |-> value) |-- intArray.seg p i (i+1) [value] := by
  exact intArray.seg_single p i value

private theorem prefix_step (l pref : List Int) (i : Int) (hp : PrefixArrayPrefix l pref i) (hi : i < Zlength l) :
    PrefixArrayPrefix l (pref ++ [Znth i pref 0+Znth i l 0]) (i+1) := by
  obtain ⟨hi0,hil,hlen,hzero,hstep⟩ := hp
  have hget : ∀ j, 0 ≤ j ∧ j < Zlength pref →
      Znth j (pref ++ [Znth i pref 0+Znth i l 0]) 0 = Znth j pref 0 := by
    intro j hj
    exact ListLib.app_Znth1 0 pref _ j hj
  refine ⟨by omega,by omega,?_,?_,?_⟩
  · rw [Zlength_app,Zlength_cons,Zlength_nil,hlen]; omega
  · rw [hget 0 ⟨le_refl _,by omega⟩,hzero]
  · intro j hj
    by_cases he : j < i
    · rw [hget (j+1) ⟨by omega,by omega⟩,hget j ⟨by omega,by omega⟩]
      exact hstep j ⟨hj.1,he⟩
    · have heq : j = i := by omega
      subst j
      rw [app_Znth2 0 pref _ (i+1) (by omega),hlen]
      simp only [Int.sub_self,Znth0_cons]
      rw [hget i ⟨hi0,by omega⟩]

theorem proof_of_build_prefix_safety_wit_6 : build_prefix_safety_wit_6 := by
  unfold build_prefix_safety_wit_6
  left
  intro pre_pre n_pre arr_pre l pref i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hp := PrefixArrayPrefix_entry_abs_bound l pref i i PreH7 (fun idx hh => PreH8 idx ⟨hh.1,by omega⟩) ⟨PreH5,le_refl _⟩
  have hl := PreH8 i ⟨PreH5,PreH1⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega

theorem proof_of_build_prefix_entail_wit_1 : build_prefix_entail_wit_1 := by
  unfold build_prefix_entail_wit_1
  left
  intro pre_pre n_pre arr_pre l ps PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  refine Automation.exp_right_rule (CRules := naive_C_Rules) [0] ?_
  split_pure_spatial
  · sep_apply (cell_to_seg pre_pre 0 0)
    simp only [Int.zero_add]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | rfl
    | (refine ⟨by omega,by omega,rfl,rfl,?_⟩; intro j hj; omega)

theorem proof_of_build_prefix_entail_wit_2 : build_prefix_entail_wit_2 := by
  unfold build_prefix_entail_wit_2
  left
  intro pre_pre n_pre arr_pre l pref_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pref_2 ?_
  split_pure_spatial
  · simp only [Int.zero_add]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega

theorem proof_of_build_prefix_entail_wit_3 : build_prefix_entail_wit_3 := by
  unfold build_prefix_entail_wit_3
  left
  intro pre_pre n_pre arr_pre l pref_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (pref_2 ++ [Znth (i-0) pref_2 0+Znth i l 0]) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (simpa only [Int.sub_zero] using prefix_step l pref_2 i PreH7 (by omega))

theorem proof_of_build_prefix_return_wit_1 : build_prefix_return_wit_1 := by
  unfold build_prefix_return_wit_1
  left
  intro pre_pre n_pre arr_pre l pref i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : i = n_pre := by omega
  subst i
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pref ?_
  split_pure_spatial
  · sep_apply (intArray.undef_seg_empty pre_pre (n_pre+1))
    have hseg : intArray.seg pre_pre 0 (n_pre+1) pref |-- intArray.full pre_pre (n_pre+1) pref := by
      simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.seg_to_full pre_pre 0 (n_pre+1) pref
    sep_apply hseg
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | (unfold PrefixSums; rw [PreH4]; exact PreH7)
    | (intro idx hi; have hb := PrefixArrayPrefix_entry_abs_bound l pref n_pre idx PreH7 PreH8 ⟨hi.1,by omega⟩; constructor <;> omega)

theorem proof_of_superPiano_safety_wit_10 : superPiano_safety_wit_10 := by
  unfold superPiano_safety_wit_10
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps ans st_slots vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hv := ValidNodeFields_value_int_bound l ps n_pre L_pre R_pre value start lo hi best PreH19 PreH18 PreH11 PreH12 PreH41 PreH31
  have ht := frontier_total_int64_bound l ps n_pre L_pre R_pre chosen t total (sublist 0 hsize pop_slots) PreH19 PreH18 PreH11 PreH41 PreH29
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega

theorem proof_of_superPiano_safety_wit_23 : superPiano_safety_wit_23 := by
  unfold superPiano_safety_wit_23
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hh := PrefixSums_diff_int_bounds l query_ps n_pre retval (start-1) PreH26 PreH25 PreH18 PreH48 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega

theorem proof_of_superPiano_safety_wit_39 : superPiano_safety_wit_39 := by
  unfold superPiano_safety_wit_39
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have hh := PrefixSums_diff_int_bounds l query_ps n_pre retval (start-1) PreH33 PreH32 PreH25 PreH55 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega

theorem proof_of_superPiano_safety_wit_42 : superPiano_safety_wit_42 := by
  unfold superPiano_safety_wit_42
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have hh := PrefixSums_diff_int_bounds l query_ps n_pre retval (start-1) PreH27 PreH26 PreH19 PreH49 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega

theorem proof_of_superPiano_entail_wit_1 : superPiano_entail_wit_1 := by
  unfold superPiano_entail_wit_1
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 ps_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he := PrefixSums_functional l ps_3 ps_2 PreH1 PreH11
  subst ps_3
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (zeros ((n_pre+1)*ST_LEVELS)) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (unfold zeros; simp only [Zlength,List.length_replicate]; exact Int.toNat_of_nonneg (by unfold ST_LEVELS; omega))

theorem proof_of_superPiano_entail_wit_3 : superPiano_entail_wit_3 := by
  unfold superPiano_entail_wit_3
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 st_slots_2 heap_cap vals_2 starts_2 los_2 his_2 bests_2 slots_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega

theorem proof_of_superPiano_entail_wit_4 : superPiano_entail_wit_4 := by
  unfold superPiano_entail_wit_4
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 st_slots_2 slots_2 vals_2 starts_2 los_2 his_2 bests_2 heap_cap hsize PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  unfold InitialFrontierState at PreH19
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega

theorem proof_of_superPiano_entail_wit_5 : superPiano_entail_wit_5 := by
  unfold superPiano_entail_wit_5
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 st_slots_2 slots_2 vals_2 starts_2 los_2 his_2 bests_2 heap_cap hsize total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (rw [PreH11]; exact PreH20)

theorem proof_of_superPiano_entail_wit_6 : superPiano_entail_wit_6 := by
  unfold superPiano_entail_wit_6
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l total hsize t ans_2 st_slots_2 ps_2 heap_cap slots_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 retval retval_2 retval_3 retval_4 retval_5 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hsize_pos : 0 < hsize := PreH38 PreH16
  have hlen : hsize ≤ Zlength slots_2 := by omega
  have ht := frontier_state_top_node_valid ps_2 n_pre L_pre R_pre chosen_2 t total slots_2 hsize hsize_pos hlen PreH36
  have hv : ValidNodeFields ps_2 n_pre L_pre R_pre retval retval_2 retval_3 retval_4 retval_5 := by
    rw [PreH10,PreH7,PreH4,PreH1,PreH13]
    exact ht
  have hv' := hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv'
  have hmin := hv'.2.2.2.2.2.1.trans (min_le_left _ _)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega

theorem proof_of_superPiano_entail_wit_7 : superPiano_entail_wit_7 := by
  unfold superPiano_entail_wit_7
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_both_children query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best retval retval_2 <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)

theorem proof_of_superPiano_entail_wit_8 : superPiano_entail_wit_8 := by
  unfold superPiano_entail_wit_8
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_left_only query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best retval <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)

theorem proof_of_superPiano_entail_wit_9 : superPiano_entail_wit_9 := by
  unfold superPiano_entail_wit_9
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_singleton query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best  <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)

theorem proof_of_superPiano_entail_wit_13 : superPiano_entail_wit_13 := by
  unfold superPiano_entail_wit_13
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left has_right t hsize right_best hi best start right_value left_best lo left_value total value push_ps push_slots push_vals push_starts push_los push_his push_bests vals_out starts_out los_out his_out bests_out slots_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) push_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_left_keeps_right_pending; assumption; assumption)

theorem proof_of_superPiano_entail_wit_14 : superPiano_entail_wit_14 := by
  unfold superPiano_entail_wit_14
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_right_only query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best retval <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)

theorem proof_of_superPiano_entail_wit_15_4 : superPiano_entail_wit_15_4 := by
  unfold superPiano_entail_wit_15_4
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left has_right t hsize left_best best lo start left_value total hi right_best right_value value push_ps push_slots push_vals push_starts push_los push_his push_bests vals_out starts_out los_out his_out bests_out slots_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have hv := PreH47
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  
  have hleft : -2147483648 ≤ left_value ∧ left_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l push_ps n_pre L_pre R_pre left_value start lo (best-1) left_best
    all_goals assumption
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) push_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_single_pending_forms_frontier; assumption; assumption)

theorem proof_of_superPiano_entail_wit_15_3 : superPiano_entail_wit_15_3 := by
  unfold superPiano_entail_wit_15_3
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 st_slots_2 slots_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 heap_cap has_left has_right left_best left_value right_best right_value t hsize total best start lo hi value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hv := PreH34
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega

theorem proof_of_superPiano_entail_wit_15_2 : superPiano_entail_wit_15_2 := by
  unfold superPiano_entail_wit_15_2
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left left_best left_value has_right t hsize right_best hi best start right_value total lo value right_ps right_slots right_vals right_starts right_los right_his right_bests vals_out starts_out los_out his_out bests_out slots_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
  have hv := PreH45
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  
  have hright : -2147483648 ≤ right_value ∧ right_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre right_value start (best+1) hi right_best
    all_goals assumption
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) right_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_single_pending_forms_frontier; assumption; assumption)

theorem proof_of_superPiano_entail_wit_15_1 : superPiano_entail_wit_15_1 := by
  unfold superPiano_entail_wit_15_1
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left has_right t hsize right_best hi best start right_value total lo left_best left_value value right_ps right_slots right_vals right_starts right_los right_his right_bests vals_out starts_out los_out his_out bests_out slots_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hv := PreH52
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  have hvl := PreH51
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hvl
  have hleft : -2147483648 ≤ left_value ∧ left_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre left_value start lo (best-1) left_best
    all_goals assumption
  have hright : -2147483648 ≤ right_value ∧ right_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre right_value start (best+1) hi right_best
    all_goals assumption
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) right_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_single_pending_forms_frontier; assumption; assumption)

theorem proof_of_superPiano_entail_wit_16 : superPiano_entail_wit_16 := by
  unfold superPiano_entail_wit_16
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 st_slots_2 slots_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 heap_cap has_left has_right left_best right_best left_value right_value t hsize total best start hi lo value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (ChordCode n_pre start best::chosen_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (intro hmore; exact frontier_state_nonempty_if_more_choices_remain ps_2 n_pre L_pre R_pre k_pre ans_2 (ChordCode n_pre start best::chosen_2) (t+1) total slots_2 hsize PreH12 PreH32 PreH29 (by omega) hmore)

theorem proof_of_superPiano_return_wit_1 : superPiano_return_wit_1 := by
  unfold superPiano_return_wit_1
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l chosen total hsize t vals_2 starts_2 los_2 his_2 bests_2 slots_2 ans st_slots_2 ps_2 heap_cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · rw [← PreH9]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_state_complete_implies_answer ps_2 n_pre L_pre R_pre k_pre chosen total (sublist 0 hsize slots_2); simpa only [show t=k_pre by omega] using PreH21)

theorem proof_of_superPiano_partial_solve_wit_1_pure : superPiano_partial_solve_wit_1_pure := by
  unfold superPiano_partial_solve_wit_1_pure
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps_2 ans PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega | (intro idx hi; apply PreH10; omega)

theorem proof_of_superPiano_partial_solve_wit_2_pure : superPiano_partial_solve_wit_2_pure := by
  unfold superPiano_partial_solve_wit_2_pure
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l heap_cap ps ans st_slots PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  dsimp only [PrefixSums,PrefixArrayPrefix] at PreH10
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_3_pure : superPiano_partial_solve_wit_3_pure := by
  unfold superPiano_partial_solve_wit_3_pure
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre st_pre prefix_pre R_pre L_pre k_pre n_pre arr_pre l ps ans st_slots heap_cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  dsimp only [PrefixSums,PrefixArrayPrefix] at PreH10
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega

end SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_proof_manual
