import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_goal
import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open split_array_largest_sum_goal split_array_largest_sum_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem quot_half_lt (a : Int) (ha : 0 < a) : Z.quot a 2 < a := by
  by_cases he : a = 1
  · subst a; decide
  · have h := Z.quot_le_upper_bound a 2 (a-1) (by omega) (by omega)
    omega

theorem proof_of_check_entail_wit_1 : check_entail_wit_1 := by
  unfold check_entail_wit_1
  right
  intro cap_pre m_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH8 | exact prefix_split_state_zero l cap_pre PreH5

theorem proof_of_check_entail_wit_2_1 : check_entail_wit_2_1 := by
  unfold check_entail_wit_2_1
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact prefix_split_state_step_over_cap _ _ _ _ _ _ PreH10 PreH11 PreH12 PreH3 PreH2 PreH1 PreH18

theorem proof_of_check_entail_wit_2_2 : check_entail_wit_2_2 := by
  unfold check_entail_wit_2_2
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact PrefixSplitState_extend i cnt cur ⟨PreH12, by omega⟩ ⟨(PreH11 i ⟨PreH12, PreH3⟩).1, PreH2⟩ PreH1 PreH18

theorem proof_of_check_return_wit_1 : check_return_wit_1 := by
  unfold check_return_wit_1
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _ cnt' cur' hs
    have hpre : PrefixSplitState l cap_pre (Zlength l) cnt cur := by
      rw [show Zlength l = i by omega]; exact PreH17
    have hh := PrefixSplitState_unique _ _ _ _ _ _ _ hpre hs
    omega

theorem proof_of_check_return_wit_2 : check_return_wit_2 := by
  unfold check_return_wit_2
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _
    exact ⟨cnt, cur, by rw [show Zlength l = i by omega]; exact PreH17, PreH1⟩

theorem proof_of_check_return_wit_3 : check_return_wit_3 := by
  unfold check_return_wit_3
  right
  intro cap_pre m_pre n_pre l cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _ cnt' cur' hs
    have hh := PrefixSplitState_items_bound _ _ _ _ _ hs i ⟨PreH11, by omega⟩
    omega

theorem proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3 := by
  unfold splitArrayLargestSum_safety_wit_3
  right
  intro m_pre n_pre arr_pre l res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hm := mid_quot_bounds left right PreH8 PreH1 PreH9
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7 := by
  unfold splitArrayLargestSum_safety_wit_7
  right
  intro m_pre n_pre arr_pre l res right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hm := mid_quot_bounds left right PreH12 PreH5 PreH13
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1 := by
  unfold splitArrayLargestSum_entail_wit_1
  right
  intro m_pre n_pre l ans PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH7 | omega

theorem proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1 := by
  unfold splitArrayLargestSum_entail_wit_2_1
  right
  intro m_pre n_pre l res_2 right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hm := mid_quot_bounds left right PreH12 PreH5 PreH13
  have hq := Z.quot_pos (right-left) 2 (by omega) (by omega)
  have hb := minmax_can_lower_bound l m_pre res_2 (left+Z.quot (right-left) 2)
    ⟨PreH8, by omega⟩ (by intro k hk; exact (PreH11 k ⟨hk.1, by omega⟩).1) PreH17 (PreH3 (by omega))
  refine Automation.exp_right_rule (CRules := naive_C_Rules) res_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH17 | omega

theorem proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2 := by
  unfold splitArrayLargestSum_entail_wit_2_2
  right
  intro m_pre n_pre l res_2 right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hm := mid_quot_bounds left right PreH12 PreH5 PreH13
  have hq := quot_half_lt (right-left) (by omega)
  have hb := minmax_cannot_upper_bound l m_pre res_2 (left+Z.quot (right-left) 2) hm.1
    (by intro k hk; exact (PreH11 k ⟨hk.1, by omega⟩).1) PreH17 (PreH4 PreH18)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) res_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH17 | omega

theorem proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure := by
  unfold splitArrayLargestSum_partial_solve_wit_1_pure
  right
  intro m_pre n_pre arr_pre l res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hm := mid_quot_bounds left right PreH18 PreH11 PreH19
  split_pures <;> dump_pre_spatial
  all_goals first | exact PreH17 | omega

theorem proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1 := by
  unfold splitArrayLargestSum_return_wit_1
  right
  intro m_pre n_pre l res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [show left = res by omega]; exact PreH13

end SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_proof_manual
