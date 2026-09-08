import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_goal
import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open modular_power_lib

theorem proof_of_modular_power_entail_wit_1_split_goal_1 : modular_power_entail_wit_1_split_goal_1 := by
  pre_process
  all_goals
    simp [ModularPowerProgress]

theorem proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1 := by
  pre_process
  all_goals
    have hprod := bounded_product a_pre a_pre modulus_pre (by omega) (by omega) (by omega)
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_modular_power_entail_wit_1_split_goal_1 modulus_pre b_pre a_pre) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_1 : modular_power_entail_wit_2_1_split_goal_1 := by
  pre_process
  all_goals
    simp only [rem_eq_mod b 2 (by omega) (by decide), rem_eq_mod (a*a) modulus_pre (by omega) (by omega), rem_eq_mod (result*a) modulus_pre (by omega) (by omega), zdiv_equiv b 2 (by omega) (by decide)] at *
    apply modular_power_progress_odd_step__loop_transitions <;> first | assumption | (unfold Z.modulo at *; omega)

theorem proof_of_modular_power_entail_wit_2_1_split_goal_2 : modular_power_entail_wit_2_1_split_goal_2 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_3 : modular_power_entail_wit_2_1_split_goal_3 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_4 : modular_power_entail_wit_2_1_split_goal_4 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_5 : modular_power_entail_wit_2_1_split_goal_5 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_6 : modular_power_entail_wit_2_1_split_goal_6 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_7 : modular_power_entail_wit_2_1_split_goal_7 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_8 : modular_power_entail_wit_2_1_split_goal_8 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_9 : modular_power_entail_wit_2_1_split_goal_9 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_10 : modular_power_entail_wit_2_1_split_goal_10 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1_split_goal_11 : modular_power_entail_wit_2_1_split_goal_11 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_1 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_2 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_3 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_4 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_5 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_6 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_7 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_8 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_9 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_10 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_1_split_goal_11 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_1 : modular_power_entail_wit_2_2_split_goal_1 := by
  pre_process
  all_goals
    simp only [rem_eq_mod b 2 (by omega) (by decide), rem_eq_mod (a*a) modulus_pre (by omega) (by omega), rem_eq_mod (result*a) modulus_pre (by omega) (by omega), zdiv_equiv b 2 (by omega) (by decide)] at *
    have hbmod := Int.fmod_nonneg_of_pos b (show (0 : Int) < 2 by decide)
    have hbmodlt := Int.fmod_lt_of_pos b (show (0 : Int) < 2 by decide)
    apply modular_power_progress_even_step__loop_transitions <;> first | assumption | (unfold Z.modulo at *; omega)

theorem proof_of_modular_power_entail_wit_2_2_split_goal_2 : modular_power_entail_wit_2_2_split_goal_2 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_3 : modular_power_entail_wit_2_2_split_goal_3 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_4 : modular_power_entail_wit_2_2_split_goal_4 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_5 : modular_power_entail_wit_2_2_split_goal_5 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_6 : modular_power_entail_wit_2_2_split_goal_6 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_7 : modular_power_entail_wit_2_2_split_goal_7 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_8 : modular_power_entail_wit_2_2_split_goal_8 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2_split_goal_9 : modular_power_entail_wit_2_2_split_goal_9 := by
  pre_process
  all_goals
    have ha_rem := rem_nonneg_bounds (a*a) modulus_pre (by omega) (by omega)
    have hr_rem := rem_nonneg_bounds (result*a) modulus_pre (by omega) (by omega)
    have hprod := bounded_product (Z.rem (result*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) hr_rem ha_rem
    have hsquare := bounded_product (Z.rem (a*a) modulus_pre) (Z.rem (a*a) modulus_pre) modulus_pre (by omega) ha_rem ha_rem
    have hevenprod := bounded_product result (Z.rem (a*a) modulus_pre) modulus_pre (by omega) (by omega) ha_rem
    have hq0 := Z.quot_pos b 2 (by omega) (by decide)
    have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_1 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_2 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_3 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_4 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_5 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_6 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_7 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_8 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (apply (proof_of_modular_power_entail_wit_2_2_split_goal_9 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

theorem proof_of_modular_power_return_wit_1_split_goal_1 : modular_power_return_wit_1_split_goal_1 := by
  pre_process
  all_goals
    have hb : b = 0 := by omega
    subst b
    unfold ModularPowerProgress at *
    unfold ModularPower
    simpa only [Z.pow, Int.pow_zero, Int.mul_one, Z.modulo, Int.fmod_eq_of_lt (show 0 ≤ result by omega) (show result < modulus_pre by omega)] using PreH17

theorem proof_of_modular_power_return_wit_1 : modular_power_return_wit_1 := by
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_modular_power_return_wit_1_split_goal_1 modulus_pre b_pre a_pre result b a) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)
      | grind

end SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_proof_manual
