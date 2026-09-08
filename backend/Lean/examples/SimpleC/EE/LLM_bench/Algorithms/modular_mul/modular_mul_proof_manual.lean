import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_goal
import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open modular_mul_lib

theorem proof_of_modular_mul_entail_wit_1_1_split_goal_1 : modular_mul_entail_wit_1_1_split_goal_1 := by
  pre_process
  all_goals
    refine ⟨0, ?_⟩
    grind

theorem proof_of_modular_mul_entail_wit_1_1 : modular_mul_entail_wit_1_1 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_entail_wit_1_1_split_goal_1 modulus_pre b_pre a_pre) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_mul_entail_wit_1_2_split_goal_1 : modular_mul_entail_wit_1_2_split_goal_1 := by
  pre_process
  all_goals
    refine ⟨0, ?_⟩
    grind

theorem proof_of_modular_mul_entail_wit_1_2 : modular_mul_entail_wit_1_2 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_entail_wit_1_2_split_goal_1 modulus_pre b_pre a_pre) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_1 : modular_mul_entail_wit_2_1_split_goal_1 := by
  pre_process
  all_goals
    simp only [rem_eq_mod b 2 (by omega) (by decide), zdiv_equiv b 2 (by omega) (by decide)] at *
    subst flag
    apply modular_mul_progress_odd_step__odd_transition <;> first | assumption | omega

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_2 : modular_mul_entail_wit_2_1_split_goal_2 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_3 : modular_mul_entail_wit_2_1_split_goal_3 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_4 : modular_mul_entail_wit_2_1_split_goal_4 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_5 : modular_mul_entail_wit_2_1_split_goal_5 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_6 : modular_mul_entail_wit_2_1_split_goal_6 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_7 : modular_mul_entail_wit_2_1_split_goal_7 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_8 : modular_mul_entail_wit_2_1_split_goal_8 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_9 : modular_mul_entail_wit_2_1_split_goal_9 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_10 : modular_mul_entail_wit_2_1_split_goal_10 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_11 : modular_mul_entail_wit_2_1_split_goal_11 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_12 : modular_mul_entail_wit_2_1_split_goal_12 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1_split_goal_13 : modular_mul_entail_wit_2_1_split_goal_13 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_1 : modular_mul_entail_wit_2_1 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_1 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_2 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_3 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_4 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_5 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_6 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_7 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_8 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_9 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_10 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_11 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_12 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_1_split_goal_13 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_1 : modular_mul_entail_wit_2_2_split_goal_1 := by
  pre_process
  all_goals
    simp only [rem_eq_mod b 2 (by omega) (by decide), zdiv_equiv b 2 (by omega) (by decide)] at *
    subst flag
    apply modular_mul_progress_odd_step__odd_transition <;> first | assumption | omega

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_2 : modular_mul_entail_wit_2_2_split_goal_2 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_3 : modular_mul_entail_wit_2_2_split_goal_3 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_4 : modular_mul_entail_wit_2_2_split_goal_4 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_5 : modular_mul_entail_wit_2_2_split_goal_5 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_6 : modular_mul_entail_wit_2_2_split_goal_6 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_7 : modular_mul_entail_wit_2_2_split_goal_7 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_8 : modular_mul_entail_wit_2_2_split_goal_8 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_9 : modular_mul_entail_wit_2_2_split_goal_9 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_10 : modular_mul_entail_wit_2_2_split_goal_10 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_11 : modular_mul_entail_wit_2_2_split_goal_11 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_12 : modular_mul_entail_wit_2_2_split_goal_12 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2_split_goal_13 : modular_mul_entail_wit_2_2_split_goal_13 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_2 : modular_mul_entail_wit_2_2 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_1 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_2 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_3 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_4 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_5 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_6 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_7 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_8 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_9 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_10 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_11 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_12 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_2_split_goal_13 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_1 : modular_mul_entail_wit_2_3_split_goal_1 := by
  pre_process
  all_goals
    have hbrem := rem_nonneg_bounds b 2 (by omega) (by decide)
    subst flag
    apply modular_mul_progress_even_step__even_transition <;> first | assumption | omega

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_2 : modular_mul_entail_wit_2_3_split_goal_2 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_3 : modular_mul_entail_wit_2_3_split_goal_3 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_4 : modular_mul_entail_wit_2_3_split_goal_4 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_5 : modular_mul_entail_wit_2_3_split_goal_5 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_6 : modular_mul_entail_wit_2_3_split_goal_6 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_7 : modular_mul_entail_wit_2_3_split_goal_7 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_8 : modular_mul_entail_wit_2_3_split_goal_8 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3_split_goal_9 : modular_mul_entail_wit_2_3_split_goal_9 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_3 : modular_mul_entail_wit_2_3 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_1 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_2 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_3 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_4 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_5 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_6 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_7 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_8 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_3_split_goal_9 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_1 : modular_mul_entail_wit_2_4_split_goal_1 := by
  pre_process
  all_goals
    have hbrem := rem_nonneg_bounds b 2 (by omega) (by decide)
    subst flag
    apply modular_mul_progress_even_step__even_transition <;> first | assumption | omega

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_2 : modular_mul_entail_wit_2_4_split_goal_2 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_3 : modular_mul_entail_wit_2_4_split_goal_3 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_4 : modular_mul_entail_wit_2_4_split_goal_4 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_5 : modular_mul_entail_wit_2_4_split_goal_5 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_6 : modular_mul_entail_wit_2_4_split_goal_6 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_7 : modular_mul_entail_wit_2_4_split_goal_7 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_8 : modular_mul_entail_wit_2_4_split_goal_8 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4_split_goal_9 : modular_mul_entail_wit_2_4_split_goal_9 := by
  pre_process
  all_goals
    have ha_rem := rem_bounds (a+a) modulus_pre (by omega)
    have hr_rem := rem_bounds (res+a) modulus_pre (by omega)
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_mul_entail_wit_2_4 : modular_mul_entail_wit_2_4 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_1 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_2 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_3 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_4 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_5 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_6 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_7 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_8 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (apply (proof_of_modular_mul_entail_wit_2_4_split_goal_9 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_mul_return_wit_1_split_goal_1 : modular_mul_return_wit_1_split_goal_1 := by
  pre_process
  all_goals
    subst flag
    apply modular_mul_progress_finish__final_result (a := a) (b := b) <;> first | assumption | omega

theorem proof_of_modular_mul_return_wit_1 : modular_mul_return_wit_1 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_return_wit_1_split_goal_1 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_mul_return_wit_2_split_goal_1 : modular_mul_return_wit_2_split_goal_1 := by
  pre_process
  all_goals
    subst flag
    apply modular_mul_progress_finish__final_result (a := a) (b := b) <;> first | assumption | omega

theorem proof_of_modular_mul_return_wit_2 : modular_mul_return_wit_2 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals try (simp only [PreH11, PreH10])
    all_goals first
      | (apply (proof_of_modular_mul_return_wit_2_split_goal_1 modulus_pre b_pre a_pre res a flag b) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

end SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_proof_manual
