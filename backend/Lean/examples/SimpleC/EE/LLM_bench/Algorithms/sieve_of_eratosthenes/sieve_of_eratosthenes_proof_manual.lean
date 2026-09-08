import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_goal
import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_proof_auto

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open sieve_of_eratosthenes_goal sieve_of_eratosthenes_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- The generated residual branch uses real SL preprocessing and Goal_apply.
-- This library version needs explicit arguments and pure-context extraction.
theorem proof_of_solve_entail_wit_1_split_goal_1 : solve_entail_wit_1_split_goal_1 := by
  unfold solve_entail_wit_1_split_goal_1
  intro n_pre initial PreH1 PreH2 PreH3
  exact SieveInitPrefix_start__sieve_invariants n_pre initial PreH3

theorem proof_of_solve_entail_wit_1 : solve_entail_wit_1 := by
  unfold solve_entail_wit_1
  right
  intro n_pre initial PreH1 PreH2 PreH3
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_1_split_goal_1 n_pre initial PreH1 PreH2 PreH3)

theorem proof_of_solve_entail_wit_2_split_goal_1 : solve_entail_wit_2_split_goal_1 := by
  unfold solve_entail_wit_2_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact SieveInitPrefix_step__sieve_invariants n_pre i current_2 PreH4 PreH1 PreH6

theorem proof_of_solve_entail_wit_2 : solve_entail_wit_2 := by
  unfold solve_entail_wit_2
  right
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_2_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_solve_entail_wit_3_split_goal_1 : solve_entail_wit_3_split_goal_1 := by
  unfold solve_entail_wit_3_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact SieveInitPrefix_finish__sieve_invariants n_pre i current_2 PreH2 PreH1 PreH5 PreH6

theorem proof_of_solve_entail_wit_3 : solve_entail_wit_3 := by
  unfold solve_entail_wit_3
  right
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_3_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_solve_entail_wit_5_split_goal_1 : solve_entail_wit_5_split_goal_1 := by
  unfold solve_entail_wit_5_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact SieveStage_mark_start__sieve_invariants n_pre i current_2 PreH5 PreH2 PreH7

theorem proof_of_solve_entail_wit_5 : solve_entail_wit_5 := by
  unfold solve_entail_wit_5
  right
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_5_split_goal_1 n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_solve_entail_wit_6_split_goal_1 : solve_entail_wit_6_split_goal_1 := by
  unfold solve_entail_wit_6_split_goal_1
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact SieveMarkState_step__sieve_invariants n_pre i j current_2 PreH1 PreH8

theorem proof_of_solve_entail_wit_6 : solve_entail_wit_6 := by
  unfold solve_entail_wit_6
  right
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_6_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_solve_entail_wit_7_split_goal_1 : solve_entail_wit_7_split_goal_1 := by
  unfold solve_entail_wit_7_split_goal_1
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact SieveMarkState_finish__sieve_invariants n_pre i j current_2 PreH1 PreH8

theorem proof_of_solve_entail_wit_7 : solve_entail_wit_7 := by
  unfold solve_entail_wit_7
  right
  intro n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_7_split_goal_1 n_pre current_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_solve_entail_wit_8_2_split_goal_1 : solve_entail_wit_8_2_split_goal_1 := by
  unfold solve_entail_wit_8_2_split_goal_1
  intro n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact SieveStage_skip_composite__sieve_invariants n_pre i current_2 PreH5 PreH2 PreH1 PreH7

theorem proof_of_solve_entail_wit_8_2 : solve_entail_wit_8_2 := by
  unfold solve_entail_wit_8_2
  left
  intro f_pre n_pre current_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  Exists current_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact SieveStage_skip_composite__sieve_invariants n_pre i current_2 PreH5 PreH2 PreH1 PreH7

theorem proof_of_solve_entail_wit_10_split_goal_1 : solve_entail_wit_10_split_goal_1 := by
  unfold solve_entail_wit_10_split_goal_1
  intro n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact SieveStage_implies_PrimeIndicatorList n_pre i current PreH1 PreH6

theorem proof_of_solve_entail_wit_10 : solve_entail_wit_10 := by
  unfold solve_entail_wit_10
  right
  intro n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals Goal_apply (proof_of_solve_entail_wit_10_split_goal_1 n_pre current i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

end SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_proof_manual
