import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_goal
import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_proof_auto

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open container_with_most_water_linear_goal container_with_most_water_linear_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_maxAreaLinear_entail_wit_1_split_goal_1 : maxAreaLinear_entail_wit_1_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_1_split_goal_1
  intro heightSize_pre height_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact PreH7

theorem proof_of_maxAreaLinear_entail_wit_1_split_goal_2 : maxAreaLinear_entail_wit_1_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_1_split_goal_2
  intro heightSize_pre height_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine ⟨Or.inl rfl, ?_⟩
  intro i j hp
  exact Or.inr ⟨i, j, ⟨hp, hp.1, by have := hp.2.2; omega⟩, Int.le_refl _⟩

-- Pure residual VCs use the generated right branch. Explicitly discard its empty
-- spatial context before Goal_apply, then supply the Coq split lemma arguments.
theorem proof_of_maxAreaLinear_entail_wit_1 : maxAreaLinear_entail_wit_1 := by
  unfold maxAreaLinear_entail_wit_1
  right
  intro heightSize_pre height_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_1_split_goal_1 heightSize_pre height_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_1_split_goal_2 heightSize_pre height_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_maxAreaLinear_entail_wit_2_1_split_goal_1 : maxAreaLinear_entail_wit_2_1_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_1_split_goal_1
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13

theorem proof_of_maxAreaLinear_entail_wit_2_1_split_goal_2 : maxAreaLinear_entail_wit_2_1_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_2_1_split_goal_2
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have heq : LinearContainerArea l left right = (right-left) * Znth left l 0 := by
    simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_left (Int.le_of_lt PreH2)]
  rw [← heq]
  apply linear_container_invariant_update_best__best_update l left right maximumArea PreH12
  · exact ⟨PreH7, PreH3, by omega⟩
  · rw [heq]; exact PreH1

theorem proof_of_maxAreaLinear_entail_wit_2_1_split_goal_3 : maxAreaLinear_entail_wit_2_1_split_goal_3 := by
  unfold maxAreaLinear_entail_wit_2_1_split_goal_3
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_left (Int.le_of_lt PreH2)]

theorem proof_of_maxAreaLinear_entail_wit_2_1 : maxAreaLinear_entail_wit_2_1 := by
  unfold maxAreaLinear_entail_wit_2_1
  right
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_1_split_goal_1 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_1_split_goal_2 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_1_split_goal_3 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)

theorem proof_of_maxAreaLinear_entail_wit_2_2_split_goal_1 : maxAreaLinear_entail_wit_2_2_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_2_split_goal_1
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13

theorem proof_of_maxAreaLinear_entail_wit_2_2_split_goal_2 : maxAreaLinear_entail_wit_2_2_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_2_2_split_goal_2
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have heq : LinearContainerArea l left right = (right-left) * Znth right l 0 := by
    simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_right PreH2]
  rw [← heq]
  apply linear_container_invariant_update_best__best_update l left right maximumArea PreH12
  · exact ⟨PreH7, PreH3, by omega⟩
  · rw [heq]; exact PreH1

theorem proof_of_maxAreaLinear_entail_wit_2_2_split_goal_3 : maxAreaLinear_entail_wit_2_2_split_goal_3 := by
  unfold maxAreaLinear_entail_wit_2_2_split_goal_3
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_right PreH2]

theorem proof_of_maxAreaLinear_entail_wit_2_2 : maxAreaLinear_entail_wit_2_2 := by
  unfold maxAreaLinear_entail_wit_2_2
  right
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_2_split_goal_1 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_2_split_goal_2 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_2_split_goal_3 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)

theorem proof_of_maxAreaLinear_entail_wit_2_3_split_goal_1 : maxAreaLinear_entail_wit_2_3_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_3_split_goal_1
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13

theorem proof_of_maxAreaLinear_entail_wit_2_3_split_goal_2 : maxAreaLinear_entail_wit_2_3_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_2_3_split_goal_2
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn := (PreH13 left (by omega)).1
  exact Int.mul_nonneg (by omega) hn

theorem proof_of_maxAreaLinear_entail_wit_2_3_split_goal_3 : maxAreaLinear_entail_wit_2_3_split_goal_3 := by
  unfold maxAreaLinear_entail_wit_2_3_split_goal_3
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_left (Int.le_of_lt PreH2)]

theorem proof_of_maxAreaLinear_entail_wit_2_3 : maxAreaLinear_entail_wit_2_3 := by
  unfold maxAreaLinear_entail_wit_2_3
  right
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_3_split_goal_1 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_3_split_goal_2 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_3_split_goal_3 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)

theorem proof_of_maxAreaLinear_entail_wit_2_4_split_goal_1 : maxAreaLinear_entail_wit_2_4_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_2_4_split_goal_1
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH13

theorem proof_of_maxAreaLinear_entail_wit_2_4_split_goal_2 : maxAreaLinear_entail_wit_2_4_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_2_4_split_goal_2
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn := (PreH13 right (by omega)).1
  exact Int.mul_nonneg (by omega) hn

theorem proof_of_maxAreaLinear_entail_wit_2_4_split_goal_3 : maxAreaLinear_entail_wit_2_4_split_goal_3 := by
  unfold maxAreaLinear_entail_wit_2_4_split_goal_3
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_right PreH2]

theorem proof_of_maxAreaLinear_entail_wit_2_4 : maxAreaLinear_entail_wit_2_4 := by
  unfold maxAreaLinear_entail_wit_2_4
  right
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_4_split_goal_1 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_4_split_goal_2 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_2_4_split_goal_3 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)

theorem proof_of_maxAreaLinear_entail_wit_3_1_split_goal_1 : maxAreaLinear_entail_wit_3_1_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_3_1_split_goal_1
  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH20

theorem proof_of_maxAreaLinear_entail_wit_3_1_split_goal_2 : maxAreaLinear_entail_wit_3_1_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_3_1_split_goal_2
  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  apply linear_container_invariant_advance_left__pointer_transitions l left right maximumArea
  · intro k hk
    exact (PreH20 k (by omega)).1
  · exact ⟨PreH5, PreH6, by omega⟩
  · exact PreH1
  · omega
  · exact PreH19

theorem proof_of_maxAreaLinear_entail_wit_3_1 : maxAreaLinear_entail_wit_3_1 := by
  unfold maxAreaLinear_entail_wit_3_1
  right
  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_3_1_split_goal_1 heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_3_1_split_goal_2 heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)

theorem proof_of_maxAreaLinear_entail_wit_3_2_split_goal_1 : maxAreaLinear_entail_wit_3_2_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_3_2_split_goal_1
  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH20

theorem proof_of_maxAreaLinear_entail_wit_3_2_split_goal_2 : maxAreaLinear_entail_wit_3_2_split_goal_2 := by
  unfold maxAreaLinear_entail_wit_3_2_split_goal_2
  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  apply linear_container_invariant_retreat_right__pointer_transitions l left right maximumArea
  · intro k hk
    exact (PreH20 k (by omega)).1
  · exact ⟨PreH5, PreH6, by omega⟩
  · exact PreH1
  · omega
  · exact PreH19

theorem proof_of_maxAreaLinear_entail_wit_3_2 : maxAreaLinear_entail_wit_3_2 := by
  unfold maxAreaLinear_entail_wit_3_2
  right
  intro heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_3_2_split_goal_1 heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_3_2_split_goal_2 heightSize_pre l left right width shorterHeight area maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)

theorem proof_of_maxAreaLinear_entail_wit_4_split_goal_1 : maxAreaLinear_entail_wit_4_split_goal_1 := by
  unfold maxAreaLinear_entail_wit_4_split_goal_1
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  apply linear_container_closed_invariant_maximum__final_result l left right maximumArea
  · omega
  · omega
  · intro k hk
    exact (PreH11 k (by omega)).1
  · exact PreH10

theorem proof_of_maxAreaLinear_entail_wit_4 : maxAreaLinear_entail_wit_4 := by
  unfold maxAreaLinear_entail_wit_4
  right
  intro heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxAreaLinear_entail_wit_4_split_goal_1 heightSize_pre l maximumArea right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)

end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_proof_manual
