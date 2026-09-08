import Algorithms.modular_power.lean.groundtruth.modular_power_goal
import Algorithms.modular_power.lean.groundtruth.modular_power_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.modular_power.lean.groundtruth.modular_power_proof_manual

open Algorithms.modular_power.lean
open scoped SimpleC

namespace ProofSupport

private theorem pow_fmod (x m : Int) (n : Nat) :
    ((x.fmod m)^n).fmod m = (x^n).fmod m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Int.pow_succ]
    rw [Int.mul_fmod, ih, Int.fmod_fmod, ← Int.mul_fmod]

theorem pow_mod_base__loop_transitions (x m n : Int) (_hm : m ≠ 0) (hn : 0 ≤ n) :
    Z.modulo (Z.pow (Z.modulo x m) n) m = Z.modulo (Z.pow x n) m := by
  cases n with
  | ofNat n => exact pow_fmod x m n
  | negSucc n => omega

private theorem pow_twice (a n : Int) (hn : 0 ≤ n) :
    Z.pow (a * a) n = Z.pow a (2 * n) := by
  cases n with
  | ofNat n =>
    change (a * a) ^ n = a ^ (2 * n)
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, Int.pow_add, Int.pow_succ, ih (Int.ofNat_zero_le n)]
      simp [Int.pow_succ, Int.mul_assoc]
  | negSucc n => omega

private theorem pow_succ (a n : Int) (hn : 0 ≤ n) :
    Z.pow a (n + 1) = Z.pow a n * a := by
  cases n with
  | ofNat n => exact Int.pow_succ a n
  | negSucc n => omega

theorem modular_power_progress_odd_step__loop_transitions (ob oe m a b r : Int)
    (hm : 0 < m) (hb : 0 ≤ b) (hodd : Z.modulo b 2 = 1)
    (hp : ModularPowerProgress ob oe m a b r) :
    ModularPowerProgress ob oe m (Z.modulo (a*a) m) (Z.div b 2) (Z.modulo (r*a) m) := by
  have hq : 0 ≤ Z.div b 2 := Int.fdiv_nonneg hb (by decide)
  have hdecomp : b = 2 * Z.div b 2 + 1 := by
    have := Int.fmod_add_mul_fdiv b 2
    change b.fmod 2 = 1 at hodd
    change b = 2 * b.fdiv 2 + 1
    omega
  unfold ModularPowerProgress at *
  rw [show Z.modulo (Z.modulo (r*a) m * Z.pow (Z.modulo (a*a) m) (Z.div b 2)) m =
    Z.modulo (r*a * Z.pow (a*a) (Z.div b 2)) m by
      unfold Z.modulo
      rw [Int.mul_fmod, Int.fmod_fmod]
      have hpow := pow_mod_base__loop_transitions (a*a) m (Z.div b 2) (by omega) hq
      simp only [Z.modulo] at hpow
      rw [hpow]
      rw [← Int.mul_fmod]]
  rw [pow_twice a _ hq]
  have heq : r*a * Z.pow a (2 * Z.div b 2) = r * Z.pow a b := by
    conv => rhs; rw [hdecomp, pow_succ a _ (by omega)]
    grind
  rw [heq]
  exact hp

theorem modular_power_progress_even_step__loop_transitions (ob oe m a b r : Int)
    (hm : 0 < m) (hb : 0 ≤ b) (heven : Z.modulo b 2 = 0)
    (hp : ModularPowerProgress ob oe m a b r) :
    ModularPowerProgress ob oe m (Z.modulo (a*a) m) (Z.div b 2) r := by
  have hq : 0 ≤ Z.div b 2 := Int.fdiv_nonneg hb (by decide)
  have hdecomp : b = 2 * Z.div b 2 := by
    have := Int.fmod_add_mul_fdiv b 2
    change b.fmod 2 = 0 at heven
    change b = 2 * b.fdiv 2
    omega
  unfold ModularPowerProgress at *
  calc
    _ = Z.modulo (r * Z.pow (a*a) (Z.div b 2)) m := by
      unfold Z.modulo
      rw [Int.mul_fmod]
      have hpow := pow_mod_base__loop_transitions (a*a) m (Z.div b 2) (by omega) hq
      simp only [Z.modulo] at hpow
      rw [hpow]
      rw [← Int.mul_fmod]
    _ = _ := by rw [pow_twice a _ hq, ← hdecomp]; exact hp

end ProofSupport

open ProofSupport
open Algorithms.modular_power.lean.groundtruth.modular_power_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.modular_power.lean.groundtruth.modular_power_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open ProofSupport

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

end Algorithms.modular_power.lean.groundtruth.modular_power_proof_manual
