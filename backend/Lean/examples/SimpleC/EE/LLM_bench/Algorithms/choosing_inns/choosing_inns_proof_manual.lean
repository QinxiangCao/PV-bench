import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_goal
import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open choosing_inns_goal choosing_inns_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_initCounts_entail_wit_1_split_goal_1 : initCounts_entail_wit_1_split_goal_1 := by
  unfold initCounts_entail_wit_1_split_goal_1
  intro k_pre PreH1 PreH2
  exact CountsZeroPrefix_nil


theorem proof_of_initCounts_entail_wit_1_split_goal_2 : initCounts_entail_wit_1_split_goal_2 := by
  unfold initCounts_entail_wit_1_split_goal_2
  intro k_pre PreH1 PreH2
  exact CountsZeroPrefix_nil


theorem proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1 := by
  unfold initCounts_entail_wit_1
  right
  intro k_pre PreH1 PreH2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_initCounts_entail_wit_1_split_goal_1 k_pre PreH1 PreH2
      | exact proof_of_initCounts_entail_wit_1_split_goal_2 k_pre PreH1 PreH2


theorem proof_of_initCounts_entail_wit_2_split_goal_1 : initCounts_entail_wit_2_split_goal_1 := by
  unfold initCounts_entail_wit_2_split_goal_1
  intro k_pre good_l_2 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact CountsZeroPrefix_snoc_zero good_l_2 i PreH7 PreH4


theorem proof_of_initCounts_entail_wit_2_split_goal_2 : initCounts_entail_wit_2_split_goal_2 := by
  unfold initCounts_entail_wit_2_split_goal_2
  intro k_pre good_l_2 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact CountsZeroPrefix_snoc_zero seen_l_2 i PreH6 PreH4


theorem proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2 := by
  unfold initCounts_entail_wit_2
  right
  intro k_pre good_l_2 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_initCounts_entail_wit_2_split_goal_1 k_pre good_l_2 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
      | exact proof_of_initCounts_entail_wit_2_split_goal_2 k_pre good_l_2 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7


theorem proof_of_initCounts_return_wit_1 : initCounts_return_wit_1 := by
  unfold initCounts_return_wit_1
  right
  intro k_pre good_pre seen_pre good_l_2 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have he : i = k_pre := by omega
  subst i
  Exists good_l_2 seen_l_2
  split_pure_spatial
  · sep_apply (intArray.seg_to_full seen_pre 0 k_pre seen_l_2)
    sep_apply (intArray.seg_to_full good_pre 0 k_pre good_l_2)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact CountsZeroPrefix_to_full seen_l_2 k_pre PreH6 | exact CountsZeroPrefix_to_full good_l_2 k_pre PreH7


theorem proof_of_copyCounts_entail_wit_1_split_goal_1 : copyCounts_entail_wit_1_split_goal_1 := by
  unfold copyCounts_entail_wit_1_split_goal_1
  intro k_pre good_old seen_l PreH1 PreH2 PreH3 PreH4
  exact CopyCountsPrefix_zero seen_l good_old k_pre PreH3.1 PreH4.1


theorem proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1 := by
  unfold copyCounts_entail_wit_1
  right
  intro k_pre good_old seen_l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_copyCounts_entail_wit_1_split_goal_1 k_pre good_old seen_l PreH1 PreH2 PreH3 PreH4


theorem proof_of_copyCounts_entail_wit_2_split_goal_1 : copyCounts_entail_wit_2_split_goal_1 := by
  unfold copyCounts_entail_wit_2_split_goal_1
  intro k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact CopyCountsPrefix_step_replace seen_l good_old good_cur_2 i k_pre PreH9 PreH8.1 ⟨PreH4, PreH1⟩


theorem proof_of_copyCounts_entail_wit_2_split_goal_2 : copyCounts_entail_wit_2_split_goal_2 := by
  unfold copyCounts_entail_wit_2_split_goal_2
  intro k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine ⟨?_, ?_⟩
  · simpa only [Zlength_replace_Znth] using PreH8.1
  · exact replace_Znth_preserves_bounds good_cur_2 i (Znth i seen_l 0) k_pre 0 200000 PreH8.1 ⟨PreH4, PreH1⟩
      (PreH6.2 i ⟨PreH4, PreH1⟩) PreH8.2


theorem proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2 := by
  unfold copyCounts_entail_wit_2
  right
  intro k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_copyCounts_entail_wit_2_split_goal_1 k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_copyCounts_entail_wit_2_split_goal_2 k_pre good_old seen_l good_cur_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9


theorem proof_of_copyCounts_return_wit_1_split_goal_1 : copyCounts_return_wit_1_split_goal_1 := by
  unfold copyCounts_return_wit_1_split_goal_1
  intro k_pre good_old seen_l good_cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact CopyCountsPrefix_full_eq seen_l good_old good_cur i k_pre PreH9 PreH6.1 PreH8.1 PreH1 PreH5


theorem proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1 := by
  unfold copyCounts_return_wit_1
  right
  intro k_pre good_old seen_l good_cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_copyCounts_return_wit_1_split_goal_1 k_pre good_old seen_l good_cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9


theorem proof_of_countChoosingInns_entail_wit_1_split_goal_1 : countChoosingInns_entail_wit_1_split_goal_1 := by
  unfold countChoosingInns_entail_wit_1_split_goal_1
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 PreH1 PreH2 PreH3
  exact CountsZeroFull_to_ChoosingPrefixState_zero colors_l costs_l k_pre p_pre seen_l_2 good_l_2 PreH1 PreH2


theorem proof_of_countChoosingInns_entail_wit_1_split_goal_2 : countChoosingInns_entail_wit_1_split_goal_2 := by
  unfold countChoosingInns_entail_wit_1_split_goal_2
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 PreH1 PreH2 PreH3
  apply CountsZeroFull_to_ChoosingPrefixDataSafe_zero colors_l costs_l k_pre seen_l_2 good_l_2 PreH1 PreH2
  have hc := PreH3.2.2.2.1
  have ht := PreH3.2.2.2.2.1
  omega


theorem proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1 := by
  unfold countChoosingInns_entail_wit_1
  right
  intro p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 PreH1 PreH2 PreH3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_countChoosingInns_entail_wit_1_split_goal_1 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 PreH1 PreH2 PreH3
      | exact proof_of_countChoosingInns_entail_wit_1_split_goal_2 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 PreH1 PreH2 PreH3


theorem proof_of_countChoosingInns_entail_wit_2_split_goal_1 : countChoosingInns_entail_wit_2_split_goal_1 := by
  unfold countChoosingInns_entail_wit_2_split_goal_1
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact PreH2.1.1


theorem proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2 := by
  unfold countChoosingInns_entail_wit_2
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_countChoosingInns_entail_wit_2_split_goal_1 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_1 : countChoosingInns_entail_wit_3_split_goal_1 := by
  unfold countChoosingInns_entail_wit_3_split_goal_1
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
  have hn := PreH2.1
  simp only [INT_MAX]
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_2 : countChoosingInns_entail_wit_3_split_goal_2 := by
  unfold countChoosingInns_entail_wit_3_split_goal_2
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH7.2.2.2.2 (Znth i colors_l 0) hc
  have hn := PreH2.1
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_3 : countChoosingInns_entail_wit_3_split_goal_3 := by
  unfold countChoosingInns_entail_wit_3_split_goal_3
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
  have hn := PreH2.1
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_4 : countChoosingInns_entail_wit_3_split_goal_4 := by
  unfold countChoosingInns_entail_wit_3_split_goal_4
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH7.2.2.2.2 (Znth i colors_l 0) hc
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_5 : countChoosingInns_entail_wit_3_split_goal_5 := by
  unfold countChoosingInns_entail_wit_3_split_goal_5
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH7.2.2.2.2 (Znth i colors_l 0) hc
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_6 : countChoosingInns_entail_wit_3_split_goal_6 := by
  unfold countChoosingInns_entail_wit_3_split_goal_6
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_7 : countChoosingInns_entail_wit_3_split_goal_7 := by
  unfold countChoosingInns_entail_wit_3_split_goal_7
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH7.2.2.1.2 (Znth i colors_l 0) hc
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_8 : countChoosingInns_entail_wit_3_split_goal_8 := by
  unfold countChoosingInns_entail_wit_3_split_goal_8
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH2.2.2.2.2.2.2 i ⟨PreH3, PreH1⟩
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_9 : countChoosingInns_entail_wit_3_split_goal_9 := by
  unfold countChoosingInns_entail_wit_3_split_goal_9
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  have hb := PreH2.2.2.2.2.2.2 i ⟨PreH3, PreH1⟩
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_10 : countChoosingInns_entail_wit_3_split_goal_10 := by
  unfold countChoosingInns_entail_wit_3_split_goal_10
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  omega


theorem proof_of_countChoosingInns_entail_wit_3_split_goal_11 : countChoosingInns_entail_wit_3_split_goal_11 := by
  unfold countChoosingInns_entail_wit_3_split_goal_11
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc := PreH2.2.2.2.2.2.1 i ⟨PreH3, PreH1⟩
  omega


theorem proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3 := by
  unfold countChoosingInns_entail_wit_3
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_1 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_2 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_3 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_4 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_5 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_6 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_7 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_8 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_9 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_10 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_countChoosingInns_entail_wit_3_split_goal_11 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8


theorem proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4 := by
  unfold countChoosingInns_entail_wit_4
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_l good_l_2 c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hlen := PreH4.2.2.2.1
  have hn := PreH4.1
  have hid : i < Zlength colors_l := by omega
  have hdata := ChoosingPrefixDataSafe_step_expensive colors_l costs_l i k_pre seen_l good_l_2 c PreH20 hid ⟨PreH7, PreH8⟩
  have hfull := ChoosingPrefixDataSafe_step_affordable_after_copy colors_l costs_l i k_pre seen_l good_l_2 c PreH20 hid ⟨PreH7, PreH8⟩
  have hstate := ChoosingPrefixState_step_affordable_after_copy colors_l costs_l i k_pre p_pre answer (answer + Znth c seen_l 0)
    seen_l good_l_2 (replace_Znth c (Znth c seen_l 0 + 1) seen_l) c PreH20 PreH21 ⟨PreH5, hid⟩ ⟨PreH7, PreH8⟩ PreH2 (by omega) rfl rfl
  have hbound := ChoosingPrefixState_answer_bound colors_l costs_l (i + 1) k_pre p_pre (answer + Znth c seen_l 0)
    (replace_Znth c (Znth c seen_l 0 + 1) seen_l) (replace_Znth c (Znth c seen_l 0 + 1) seen_l) n_pre hfull hstate (by omega) hn.2
  have hs200 := CountArraySafe_weaken_limit _ k_pre (i + 1) 200000 hdata.2.2.1 (by omega)
  have hg200 := CountArraySafe_weaken_limit _ k_pre (i + 1) 200000 hdata.2.2.2 (by omega)
  subst c
  Exists seen_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | assumption | omega | simpa only [Int.add_sub_cancel] using PreH21


theorem proof_of_countChoosingInns_entail_wit_5_split_goal_1 : countChoosingInns_entail_wit_5_split_goal_1 := by
  unfold countChoosingInns_entail_wit_5_split_goal_1
  intro p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hlen := PreH4.2.2.2.1
  exact ChoosingPrefixState_step_affordable_after_copy colors_l costs_l i k_pre p_pre (answer - Znth c seen_l 0) answer
    seen_l good_l seen_next_2 c PreH14 PreH16 (by omega) ⟨PreH9, PreH10⟩ PreH2 (by omega) (by omega) PreH13


theorem proof_of_countChoosingInns_entail_wit_5_split_goal_2 : countChoosingInns_entail_wit_5_split_goal_2 := by
  unfold countChoosingInns_entail_wit_5_split_goal_2
  intro p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  subst seen_next_2
  have hlen := PreH4.2.2.2.1
  exact ChoosingPrefixDataSafe_step_affordable_after_copy colors_l costs_l i k_pre seen_l good_l c PreH14 (by omega) ⟨PreH9, PreH10⟩


theorem proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5 := by
  unfold countChoosingInns_entail_wit_5
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_countChoosingInns_entail_wit_5_split_goal_1 p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_countChoosingInns_entail_wit_5_split_goal_2 p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18


theorem proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6 := by
  unfold countChoosingInns_entail_wit_6
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hlen := PreH4.2.2.2.1
  have hn := PreH4.1
  have hid : i < Zlength colors_l := by omega
  have hdata := ChoosingPrefixDataSafe_step_expensive colors_l costs_l i k_pre seen_l_2 good_l c PreH20 hid ⟨PreH7, PreH8⟩
  have hstate := ChoosingPrefixState_step_expensive colors_l costs_l i k_pre p_pre answer (answer + Znth c good_l 0)
    seen_l_2 good_l (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) c PreH20 PreH21 ⟨PreH5, hid⟩ ⟨PreH7, PreH8⟩ PreH2 (by omega) rfl rfl
  have hbound := ChoosingPrefixState_answer_bound colors_l costs_l (i + 1) k_pre p_pre (answer + Znth c good_l 0)
    (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) good_l n_pre hdata hstate (by omega) hn.2
  subst c
  Exists seen_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | assumption | omega | simpa only [Int.add_sub_cancel] using PreH21


theorem proof_of_countChoosingInns_entail_wit_8_split_goal_1 : countChoosingInns_entail_wit_8_split_goal_1 := by
  unfold countChoosingInns_entail_wit_8_split_goal_1
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : n_pre = i := by omega
  rw [he]
  exact PreH8.1


theorem proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8 := by
  unfold countChoosingInns_entail_wit_8
  right
  intro p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_countChoosingInns_entail_wit_8_split_goal_1 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8


theorem proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_1 : countChoosingInns_partial_solve_wit_1_pure_split_goal_1 := by
  unfold countChoosingInns_partial_solve_wit_1_pure_split_goal_1
  intro good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  exact PreH9.2.1.1


theorem proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_2 : countChoosingInns_partial_solve_wit_1_pure_split_goal_2 := by
  unfold countChoosingInns_partial_solve_wit_1_pure_split_goal_2
  intro good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  exact PreH9.2.1.2


theorem proof_of_countChoosingInns_partial_solve_wit_1_pure : countChoosingInns_partial_solve_wit_1_pure := by
  unfold countChoosingInns_partial_solve_wit_1_pure
  right
  intro good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_1 good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_2 good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9


theorem proof_of_countChoosingInns_partial_solve_wit_7_pure_split_goal_1 : countChoosingInns_partial_solve_wit_7_pure_split_goal_1 := by
  unfold countChoosingInns_partial_solve_wit_7_pure_split_goal_1
  intro good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l seen_next seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  dump_pre_spatial
  exact PreH17.2.1.2


theorem proof_of_countChoosingInns_partial_solve_wit_7_pure : countChoosingInns_partial_solve_wit_7_pure := by
  unfold countChoosingInns_partial_solve_wit_7_pure
  right
  intro good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l seen_next seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pures
  all_goals first
    | exact proof_of_countChoosingInns_partial_solve_wit_7_pure_split_goal_1 good_pre seen_pre p_pre k_pre n_pre costs_pre colors_pre costs_l colors_l seen_next seen_l good_l c i cost answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31

end SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_proof_manual
