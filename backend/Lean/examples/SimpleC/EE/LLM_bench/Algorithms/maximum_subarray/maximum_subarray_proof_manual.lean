import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_proof_manual

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal
open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_max_return_wit_1_split_goal_1 : max_return_wit_1_split_goal_1 := by
  intro b_pre a_pre PreH1
  exact (max_eq_left (by omega : b_pre ≤ a_pre)).symm

theorem proof_of_max_return_wit_2_split_goal_1 : max_return_wit_2_split_goal_1 := by
  intro b_pre a_pre PreH1
  exact (max_eq_right PreH1).symm

theorem proof_of_max_sub_array_entail_wit_1_split_goal_1 : max_sub_array_entail_wit_1_split_goal_1 := by
  intro n_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH5

theorem proof_of_max_sub_array_entail_wit_1_split_goal_2 : max_sub_array_entail_wit_1_split_goal_2 := by
  intro n_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  exact MaxSubarraySumPrefix_single l (by omega)

theorem proof_of_max_sub_array_entail_wit_1_split_goal_3 : max_sub_array_entail_wit_1_split_goal_3 := by
  intro n_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  exact MaxSuffixSumPrefix_single l (by omega)

theorem proof_of_max_sub_array_entail_wit_2_split_goal_1 : max_sub_array_entail_wit_2_split_goal_1 := by
  intro n_pre l cur res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH12

theorem proof_of_max_sub_array_entail_wit_3_split_goal_1 : max_sub_array_entail_wit_3_split_goal_1 := by
  intro n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13

theorem proof_of_max_sub_array_entail_wit_4_split_goal_1 : max_sub_array_entail_wit_4_split_goal_1 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH15

theorem proof_of_max_sub_array_entail_wit_4_split_goal_2 : max_sub_array_entail_wit_4_split_goal_2 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  rw [PreH1]
  exact MaxSuffixSumPrefix_step l i cur (by omega) (by omega) PreH13

theorem proof_of_max_sub_array_entail_wit_4_split_goal_3 : max_sub_array_entail_wit_4_split_goal_3 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  apply MaxSuffixSumPrefix_upper_bound l (i + 1) retval n_pre (by omega) (by omega) PreH3
  · intro k hk
    exact (PreH15 k hk).2
  · rw [PreH1]
    exact MaxSuffixSumPrefix_step l i cur (by omega) (by omega) PreH13

theorem proof_of_max_sub_array_entail_wit_4_split_goal_4 : max_sub_array_entail_wit_4_split_goal_4 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  rw [PreH1]
  exact le_trans (PreH15 i (by omega)).1 (le_max_left _ _)

theorem proof_of_max_sub_array_entail_wit_5_split_goal_1 : max_sub_array_entail_wit_5_split_goal_1 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13

theorem proof_of_max_sub_array_entail_wit_5_split_goal_2 : max_sub_array_entail_wit_5_split_goal_2 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [PreH1]
  exact MaxSubarraySumPrefix_step l i res cur PreH12 PreH11

theorem proof_of_max_sub_array_entail_wit_5_split_goal_3 : max_sub_array_entail_wit_5_split_goal_3 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [PreH1]
  exact max_le PreH10 PreH8

theorem proof_of_max_sub_array_entail_wit_5_split_goal_4 : max_sub_array_entail_wit_5_split_goal_4 := by
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [PreH1]
  exact le_trans PreH9 (le_max_left _ _)

theorem proof_of_max_sub_array_entail_wit_6_split_goal_1 : max_sub_array_entail_wit_6_split_goal_1 := by
  intro n_pre l i cur res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH12

theorem proof_of_max_sub_array_entail_wit_7_split_goal_1 : max_sub_array_entail_wit_7_split_goal_1 := by
  intro n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hi : i = n_pre := by omega
  simpa [hi] using PreH12

theorem proof_of_max_sub_array_entail_wit_7_split_goal_2 : max_sub_array_entail_wit_7_split_goal_2 := by
  intro n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hi : i = n_pre := by omega
  simpa [hi] using PreH11

theorem proof_of_max_return_wit_1 : max_return_wit_1 := by
  right
  intro b_pre a_pre PreH1
  have hs0 := proof_of_max_return_wit_1_split_goal_1 b_pre a_pre PreH1
  entailer!

theorem proof_of_max_return_wit_2 : max_return_wit_2 := by
  right
  intro b_pre a_pre PreH1
  have hs0 := proof_of_max_return_wit_2_split_goal_1 b_pre a_pre PreH1
  entailer!

theorem proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1 := by
  right
  intro n_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  have hs0 := proof_of_max_sub_array_entail_wit_1_split_goal_1 n_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  have hs1 := proof_of_max_sub_array_entail_wit_1_split_goal_2 n_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  have hs2 := proof_of_max_sub_array_entail_wit_1_split_goal_3 n_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  entailer!

theorem proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2 := by
  right
  intro n_pre l cur res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hs0 := proof_of_max_sub_array_entail_wit_2_split_goal_1 n_pre l cur res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  entailer!

theorem proof_of_max_sub_array_entail_wit_3 : max_sub_array_entail_wit_3 := by
  right
  intro n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs0 := proof_of_max_sub_array_entail_wit_3_split_goal_1 n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  entailer!

theorem proof_of_max_sub_array_entail_wit_4 : max_sub_array_entail_wit_4 := by
  right
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs0 := proof_of_max_sub_array_entail_wit_4_split_goal_1 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs1 := proof_of_max_sub_array_entail_wit_4_split_goal_2 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs2 := proof_of_max_sub_array_entail_wit_4_split_goal_3 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs3 := proof_of_max_sub_array_entail_wit_4_split_goal_4 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  entailer!

theorem proof_of_max_sub_array_entail_wit_5 : max_sub_array_entail_wit_5 := by
  right
  intro n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs0 := proof_of_max_sub_array_entail_wit_5_split_goal_1 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs1 := proof_of_max_sub_array_entail_wit_5_split_goal_2 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs2 := proof_of_max_sub_array_entail_wit_5_split_goal_3 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs3 := proof_of_max_sub_array_entail_wit_5_split_goal_4 n_pre l i cur res retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  entailer!

theorem proof_of_max_sub_array_entail_wit_6 : max_sub_array_entail_wit_6 := by
  right
  intro n_pre l i cur res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hs0 := proof_of_max_sub_array_entail_wit_6_split_goal_1 n_pre l i cur res PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  entailer!

theorem proof_of_max_sub_array_entail_wit_7 : max_sub_array_entail_wit_7 := by
  right
  intro n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs0 := proof_of_max_sub_array_entail_wit_7_split_goal_1 n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs1 := proof_of_max_sub_array_entail_wit_7_split_goal_2 n_pre l res cur i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  entailer!

end SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_proof_manual
