import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open house_robber_goal house_robber_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_rob_entail_wit_1_split_goal_1 : rob_entail_wit_1_split_goal_1 := by
  intro n_pre l PreH1 PreH2 PreH3 PreH4
  exact ⟨by have h := Zlength_nonneg l; omega, RobPrefixOpt_zero l, Or.inl ⟨rfl, rfl⟩⟩

theorem proof_of_rob_entail_wit_1_split_goal_2 : rob_entail_wit_1_split_goal_2 := by
  intro n_pre l PreH1 PreH2 PreH3 PreH4
  exact PreH4

theorem proof_of_rob_entail_wit_2_1_split_goal_1 : rob_entail_wit_2_1_split_goal_1 := by
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact house_robber_dp_step_take l n_pre i prev2 prev1 PreH5 PreH7 PreH2 PreH13 PreH1

theorem proof_of_rob_entail_wit_2_1_split_goal_2 : rob_entail_wit_2_1_split_goal_2 := by
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact house_robber_take_value_bound l n_pre i prev2 prev1 PreH5 PreH4 PreH6 PreH7 PreH2 PreH13

theorem proof_of_rob_entail_wit_2_1_split_goal_3 : rob_entail_wit_2_1_split_goal_3 := by
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH6

theorem proof_of_rob_entail_wit_2_2_split_goal_1 : rob_entail_wit_2_2_split_goal_1 := by
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact HouseRobberDPState_skip_step l i prev2 prev1 PreH13 PreH1 (by omega)

theorem proof_of_rob_entail_wit_2_2_split_goal_2 : rob_entail_wit_2_2_split_goal_2 := by
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH6

theorem proof_of_rob_entail_wit_3_split_goal_1 : rob_entail_wit_3_split_goal_1 := by
  intro n_pre l i take prev2 skip prev1 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH4

theorem proof_of_rob_return_wit_1_split_goal_1 : rob_return_wit_1_split_goal_1 := by
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : Zlength l = i := by omega
  change RobPrefixOpt l (Zlength l) prev1
  rw [he]
  exact PreH12.2.1

theorem proof_of_rob_entail_wit_1 : rob_entail_wit_1 := by
  unfold rob_entail_wit_1
  right
  intro n_pre l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_rob_entail_wit_1_split_goal_1 n_pre l PreH1 PreH2 PreH3 PreH4
    · exact proof_of_rob_entail_wit_1_split_goal_2 n_pre l PreH1 PreH2 PreH3 PreH4

theorem proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1 := by
  unfold rob_entail_wit_2_1
  right
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_rob_entail_wit_2_1_split_goal_3 n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    · exact proof_of_rob_entail_wit_2_1_split_goal_1 n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    · exact proof_of_rob_entail_wit_2_1_split_goal_2 n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13


theorem proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2 := by
  unfold rob_entail_wit_2_2
  right
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_rob_entail_wit_2_2_split_goal_1 n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    · exact proof_of_rob_entail_wit_2_2_split_goal_2 n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_rob_entail_wit_3 : rob_entail_wit_3 := by
  unfold rob_entail_wit_3
  right
  intro n_pre l i take prev2 skip prev1 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_rob_entail_wit_3_split_goal_1 n_pre l i take prev2 skip prev1 cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_rob_return_wit_1 : rob_return_wit_1 := by
  unfold rob_return_wit_1
  right
  intro n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_rob_return_wit_1_split_goal_1 n_pre l prev1 prev2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

end SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual
