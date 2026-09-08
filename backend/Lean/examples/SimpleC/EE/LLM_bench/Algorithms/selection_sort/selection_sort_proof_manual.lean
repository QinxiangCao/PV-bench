import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open selection_sort_lib

theorem proof_of_sortArray_entail_wit_1_split_goal_1 : sortArray_entail_wit_1_split_goal_1 := by
  unfold sortArray_entail_wit_1_split_goal_1
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1_split_goal_2 : sortArray_entail_wit_1_split_goal_2 := by
  unfold sortArray_entail_wit_1_split_goal_2
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1_split_goal_3 : sortArray_entail_wit_1_split_goal_3 := by
  unfold sortArray_entail_wit_1_split_goal_3
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1 := by
  unfold sortArray_entail_wit_1
  right
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_1_split_goal_1 numsSize_pre l) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_1_split_goal_3 numsSize_pre l) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_2_split_goal_1 : sortArray_entail_wit_2_split_goal_1 := by
  unfold sortArray_entail_wit_2_split_goal_1
  intro numsSize_pre l a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    intro q h
    have heq : q = i_2 := by omega
    subst q
    omega

theorem proof_of_sortArray_entail_wit_2_split_goal_2 : sortArray_entail_wit_2_split_goal_2 := by
  unfold sortArray_entail_wit_2_split_goal_2
  intro numsSize_pre l a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2 := by
  unfold sortArray_entail_wit_2
  right
  intro numsSize_pre l a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_2_split_goal_1 numsSize_pre l a_2 i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_2_split_goal_2 numsSize_pre l a_2 i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_3_1_split_goal_1 : sortArray_entail_wit_3_1_split_goal_1 := by
  unfold sortArray_entail_wit_3_1_split_goal_1
  intro numsSize_pre l a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    have hlen : Zlength a_2 = numsSize_pre := by simpa only [Zlength_replace_Znth] using PreH1
    apply increasing_sublist_intro <;> try omega
    intro p q hr
    rw [Znth_replace_Znth_Diff, Znth_replace_Znth_Diff, Znth_replace_Znth_Diff, Znth_replace_Znth_Diff]
    · exact increasing_sublist_elim a_2 0 i_2 p q (by omega) (by omega) PreH11 (by omega)
    all_goals try simp only [Zlength_replace_Znth]
    all_goals omega

theorem proof_of_sortArray_entail_wit_3_1_split_goal_2 : sortArray_entail_wit_3_1_split_goal_2 := by
  unfold sortArray_entail_wit_3_1_split_goal_2
  intro numsSize_pre l a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    have hlen : Zlength a_2 = numsSize_pre := by simpa only [Zlength_replace_Znth] using PreH1
    exact PreH10.trans (permutation_swap_Znth_lt a_2 i_2 j_2 0 (by omega))

theorem proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1 := by
  unfold sortArray_entail_wit_3_1
  right
  intro numsSize_pre l a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_3_1_split_goal_1 numsSize_pre l a_2 j_2 i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_3_1_split_goal_2 numsSize_pre l a_2 j_2 i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_4_split_goal_1 : sortArray_entail_wit_4_split_goal_1 := by
  unfold sortArray_entail_wit_4_split_goal_1
  intro numsSize_pre l a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    intro p q h
    by_cases hp : p < i_2
    · exact PreH11 p q (by omega)
    · have heq : p = i_2 := by omega
      subst p
      exact PreH12 q (by omega)

theorem proof_of_sortArray_entail_wit_4_split_goal_2 : sortArray_entail_wit_4_split_goal_2 := by
  unfold sortArray_entail_wit_4_split_goal_2
  intro numsSize_pre l a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    apply increasing_sublist_intro <;> try omega
    intro p q hr
    by_cases hq : q = i_2
    · subst q
      by_cases hp : p = i_2
      · subst p; omega
      · exact PreH11 p i_2 (by omega)
    · exact increasing_sublist_elim a_2 0 i_2 p q (by omega) (by omega) PreH10 (by omega)

theorem proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4 := by
  unfold sortArray_entail_wit_4
  right
  intro numsSize_pre l a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_4_split_goal_1 numsSize_pre l a_2 j i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_4_split_goal_2 numsSize_pre l a_2 j i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_return_wit_1_split_goal_1 : sortArray_return_wit_1_split_goal_1 := by
  unfold sortArray_return_wit_1_split_goal_1
  intro numsSize_pre l a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    have hi : i = numsSize_pre := by omega
    subst i
    rw [← PreH1] at PreH8
    simpa [sublist, Zlength] using PreH8

theorem proof_of_sortArray_return_wit_1 : sortArray_return_wit_1 := by
  unfold sortArray_return_wit_1
  right
  intro numsSize_pre l a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_return_wit_1_split_goal_1 numsSize_pre l a i) <;> assumption)
      | omega
      | int_auto

end SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_proof_manual
