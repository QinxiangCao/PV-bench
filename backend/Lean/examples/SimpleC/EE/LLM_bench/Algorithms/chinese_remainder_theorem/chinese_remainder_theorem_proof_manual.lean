import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_goal
import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open chinese_remainder_theorem_goal chinese_remainder_theorem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem normalize_negative_term (a r p result : Int) (hp : 0 < p) (hr : 0 ≤ result) :
    Z.rem (result+(Z.rem (Z.rem a p*r) p+p)) p =
    Z.modulo (result+Z.modulo (Z.modulo a p*r) p) p := by
  have hb := AUXLib.rem_bounds (Z.rem a p*r) p hp
  rw [crt_rem_eq_mod_of_nonnegative_dividend__crt_transition _ p (by omega) hp]
  change Int.fmod (result+(Z.rem (Z.rem a p*r) p+p)) p = _
  rw [← Int.add_assoc, Int.add_fmod_right]
  apply Int.add_fmod_eq_add_fmod_left
  have ht := (crt_rem_mod__crt_transition (Z.rem a p*r) p (by omega)).trans
    (crt_rem_mul_mod__crt_transition a r p (by omega))
  simpa only [Z.modulo, Int.fmod_fmod] using ht

private theorem normalize_nonnegative_term (a r p result : Int) (hp : 0 < p) (hr : 0 ≤ result)
    (ht : 0 ≤ Z.rem (Z.rem a p*r) p) :
    Z.rem (result+Z.rem (Z.rem a p*r) p) p =
    Z.modulo (result+Z.modulo (Z.modulo a p*r) p) p := by
  rw [crt_rem_eq_mod_of_nonnegative_dividend__crt_transition _ p (by omega) hp]
  rw [crt_nonnegative_rem_eq_mod__crt_transition (Z.rem a p*r) p hp ht,
    crt_rem_mul_mod__crt_transition a r p (by omega)]

-- Preserve the source residual VCs and run the SL strategy. Goal_apply needs
-- explicit arguments; pure split conclusions use dump_spatial_left, whereas
-- the store_int_range proof retains the actual coefficient cell.

theorem proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1 : chinese_remainder_theorem_safety_wit_3_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_3_split_goal_1
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simp only [INT_MAX] at *
  dump_pre_spatial
  have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
  have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) PreH3 (by omega)).1
  rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH7] at hb
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2 : chinese_remainder_theorem_safety_wit_3_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_3_split_goal_2
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simp only [INT_MIN] at *
  dump_pre_spatial
  have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
  have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) PreH3 (by omega)).1
  rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH7] at hb
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_3 : chinese_remainder_theorem_safety_wit_3 := by
  unfold chinese_remainder_theorem_safety_wit_3
  right
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1 moduli_pre remainders_pre n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2 moduli_pre remainders_pre n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | trivial

theorem proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1 : chinese_remainder_theorem_safety_wit_7_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_7_split_goal_1
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [INT_MIN] at *
  dump_pre_spatial
  left
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2 : chinese_remainder_theorem_safety_wit_7_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_7_split_goal_2
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  dump_pre_spatial
  have hb := PreH3.2.2.1 i (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_7 : chinese_remainder_theorem_safety_wit_7 := by
  unfold chinese_remainder_theorem_safety_wit_7
  right
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | trivial

theorem proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_1 : chinese_remainder_theorem_safety_wit_9_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_9_split_goal_1
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [INT_MAX] at *
  prop_apply (naive_C_Rules.store_int_range (&( "coefficient" )) x_callee_v)
  Intros_p hcoefficient
  change (-2147483648 : Int) ≤ x_callee_v ∧ x_callee_v ≤ 2147483647 at hcoefficient
  have hb := PreH5.2.2.1 i (by omega)
  have hm := PreH6.2 i x_callee_v (by omega) hcoefficient
  rw [← PreH7] at hm
  dump_pre_spatial
  rw [crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega)]
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_2 : chinese_remainder_theorem_safety_wit_9_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_9_split_goal_2
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [INT_MIN] at *
  prop_apply (naive_C_Rules.store_int_range (&( "coefficient" )) x_callee_v)
  Intros_p hcoefficient
  change (-2147483648 : Int) ≤ x_callee_v ∧ x_callee_v ≤ 2147483647 at hcoefficient
  have hb := PreH5.2.2.1 i (by omega)
  have hm := PreH6.2 i x_callee_v (by omega) hcoefficient
  rw [← PreH7] at hm
  dump_pre_spatial
  rw [crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega)]
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_9 : chinese_remainder_theorem_safety_wit_9 := by
  unfold chinese_remainder_theorem_safety_wit_9
  right
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_1 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_9_split_goal_2 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | trivial

theorem proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1 : chinese_remainder_theorem_safety_wit_11_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_11_split_goal_1
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [INT_MAX] at *
  have hb := PreH5.2.2.1 i (by omega)
  have hm := CRTInputValid_modulus_upper_bound__machine_safety remainders_l moduli_l i PreH5 (by omega)
  have hr := crt_c_rem_mul_int_bounds__machine_safety (x_callee_v * Z.quot product (Znth i moduli_l 0)) product (Znth i remainders_l 0) PreH8 PreH9 hb.2.1 (by omega)
  dump_pre_spatial
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2 : chinese_remainder_theorem_safety_wit_11_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_11_split_goal_2
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [INT_MIN] at *
  have hb := PreH5.2.2.1 i (by omega)
  have hm := CRTInputValid_modulus_upper_bound__machine_safety remainders_l moduli_l i PreH5 (by omega)
  have hr := crt_c_rem_mul_int_bounds__machine_safety (x_callee_v * Z.quot product (Znth i moduli_l 0)) product (Znth i remainders_l 0) PreH8 PreH9 hb.2.1 (by omega)
  dump_pre_spatial
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_11 : chinese_remainder_theorem_safety_wit_11 := by
  unfold chinese_remainder_theorem_safety_wit_11
  right
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | trivial

theorem proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1 : chinese_remainder_theorem_safety_wit_17_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_17_split_goal_1
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simp only [INT_MAX] at *
  have hb := AUXLib.rem_bounds (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
  dump_pre_spatial
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2 : chinese_remainder_theorem_safety_wit_17_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_17_split_goal_2
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simp only [INT_MIN] at *
  have hb := AUXLib.rem_bounds (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
  dump_pre_spatial
  omega

theorem proof_of_chinese_remainder_theorem_safety_wit_17 : chinese_remainder_theorem_safety_wit_17 := by
  unfold chinese_remainder_theorem_safety_wit_17
  right
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 : chinese_remainder_theorem_entail_wit_1_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_1_split_goal_1
  intro n_pre moduli_l remainders_l PreH1 PreH2 PreH3
  exact PreH3.1.2

theorem proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 : chinese_remainder_theorem_entail_wit_1_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_1_split_goal_2
  intro n_pre moduli_l remainders_l PreH1 PreH2 PreH3
  exact PreH3.1.1

theorem proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_3 : chinese_remainder_theorem_entail_wit_1_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_1_split_goal_3
  intro n_pre moduli_l remainders_l PreH1 PreH2 PreH3
  rfl

theorem proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_4 : chinese_remainder_theorem_entail_wit_1_split_goal_4 := by
  unfold chinese_remainder_theorem_entail_wit_1_split_goal_4
  intro n_pre moduli_l remainders_l PreH1 PreH2 PreH3
  have := PreH2.2.1
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_1 : chinese_remainder_theorem_entail_wit_1 := by
  unfold chinese_remainder_theorem_entail_wit_1
  right
  intro n_pre moduli_l remainders_l PreH1 PreH2 PreH3
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 n_pre moduli_l remainders_l PreH1 PreH2 PreH3))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 n_pre moduli_l remainders_l PreH1 PreH2 PreH3)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 n_pre moduli_l remainders_l PreH1 PreH2 PreH3))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 n_pre moduli_l remainders_l PreH1 PreH2 PreH3)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_3 n_pre moduli_l remainders_l PreH1 PreH2 PreH3))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_3 n_pre moduli_l remainders_l PreH1 PreH2 PreH3)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_4 n_pre moduli_l remainders_l PreH1 PreH2 PreH3))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_4 n_pre moduli_l remainders_l PreH1 PreH2 PreH3)
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 : chinese_remainder_theorem_entail_wit_2_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_2_split_goal_1
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
  have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) PreH3 (by omega)).1
  rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH7] at hb
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 : chinese_remainder_theorem_entail_wit_2_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_2_split_goal_2
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
  have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) PreH3 (by omega)).1
  rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH7] at hb
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 : chinese_remainder_theorem_entail_wit_2_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_2_split_goal_3
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [PreH7]
  exact (crt_prefix_product_step__product_progress moduli_l i (by omega)).symm

theorem proof_of_chinese_remainder_theorem_entail_wit_2 : chinese_remainder_theorem_entail_wit_2 := by
  unfold chinese_remainder_theorem_entail_wit_2
  right
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 : chinese_remainder_theorem_entail_wit_3_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_3_split_goal_1
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro k hk
  simp [Z.rem]

theorem proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 : chinese_remainder_theorem_entail_wit_3_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_3_split_goal_2
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro k hk
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 : chinese_remainder_theorem_entail_wit_3_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_3_split_goal_3
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hi : i = Zlength moduli_l := by omega
  rw [sublist_self moduli_l i hi] at PreH7
  exact PreH7

theorem proof_of_chinese_remainder_theorem_entail_wit_3 : chinese_remainder_theorem_entail_wit_3 := by
  unfold chinese_remainder_theorem_entail_wit_3
  right
  intro n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 n_pre moduli_l remainders_l product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : chinese_remainder_theorem_entail_wit_4_1_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_4_1_split_goal_1
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hm := (PreH6.2.2.1 i (by omega)).1
  have hq := crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega)
  rw [hq] at PreH3 ⊢
  have hz : ∀ k, (i ≤ k ∧ k < Zlength moduli_l) → Z.modulo result (Znth k moduli_l 0) = 0 := by
    intro k hk
    have hm := (PreH6.2.2.1 k (by omega)).1
    rw [← crt_rem_eq_mod_of_nonnegative_dividend__crt_transition result (Znth k moduli_l 0) PreH13 (by omega)]
    exact PreH16 k (by omega)
  have hu := crt_update_processed__crt_transition remainders_l moduli_l result i product x_callee_v y_callee_v PreH6 (by omega) PreH8 PreH9 PreH15 hz PreH3
  rw [normalize_negative_term (x_callee_v * Z.div product (Znth i moduli_l 0)) (Znth i remainders_l 0) product result (by omega) PreH13]
  exact hu

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : chinese_remainder_theorem_entail_wit_4_1_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_4_1_split_goal_2
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have ht := AUXLib.rem_bounds (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
  have hb := AUXLib.rem_nonneg_bounds (result + (Z.rem (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product + product)) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : chinese_remainder_theorem_entail_wit_4_1_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_4_1_split_goal_3
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have ht := AUXLib.rem_bounds (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
  have hb := AUXLib.rem_nonneg_bounds (result + (Z.rem (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product + product)) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1 : chinese_remainder_theorem_entail_wit_4_1 := by
  unfold chinese_remainder_theorem_entail_wit_4_1
  right
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : chinese_remainder_theorem_entail_wit_4_2_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_4_2_split_goal_1
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hm := (PreH6.2.2.1 i (by omega)).1
  have hq := crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega)
  rw [hq] at PreH3 ⊢
  have hz : ∀ k, (i ≤ k ∧ k < Zlength moduli_l) → Z.modulo result (Znth k moduli_l 0) = 0 := by
    intro k hk
    have hm := (PreH6.2.2.1 k (by omega)).1
    rw [← crt_rem_eq_mod_of_nonnegative_dividend__crt_transition result (Znth k moduli_l 0) PreH13 (by omega)]
    exact PreH16 k (by omega)
  have hu := crt_update_processed__crt_transition remainders_l moduli_l result i product x_callee_v y_callee_v PreH6 (by omega) PreH8 PreH9 PreH15 hz PreH3
  rw [hq] at PreH1
  rw [normalize_nonnegative_term (x_callee_v * Z.div product (Znth i moduli_l 0)) (Znth i remainders_l 0) product result (by omega) PreH13 PreH1]
  exact hu

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : chinese_remainder_theorem_entail_wit_4_2_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_4_2_split_goal_2
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hb := AUXLib.rem_nonneg_bounds (result + Z.rem (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : chinese_remainder_theorem_entail_wit_4_2_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_4_2_split_goal_3
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hb := AUXLib.rem_nonneg_bounds (result + Z.rem (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2 : chinese_remainder_theorem_entail_wit_4_2 := by
  unfold chinese_remainder_theorem_entail_wit_4_2
  right
  intro n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 n_pre moduli_l remainders_l result i product y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | trivial

theorem proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 : chinese_remainder_theorem_return_wit_1_split_goal_1 := by
  unfold chinese_remainder_theorem_return_wit_1_split_goal_1
  intro n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  refine ⟨⟨PreH10, by omega⟩, ?_⟩
  intro k hk
  exact PreH12 k (by omega)

theorem proof_of_chinese_remainder_theorem_return_wit_1 : chinese_remainder_theorem_return_wit_1 := by
  unfold chinese_remainder_theorem_return_wit_1
  right
  intro n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [INT_MAX, INT_MIN] at *
  have hb := crt_factor_quotient_bounds__product_progress remainders_l moduli_l i PreH13 (by omega)
  dump_pre_spatial
  rw [crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega), PreH15]
  omega

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [INT_MAX, INT_MIN] at *
  have hb := PreH13.2.2.1 i (by omega)
  dump_pre_spatial
  omega

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [INT_MAX, INT_MIN] at *
  have hb := crt_factor_quotient_bounds__product_progress remainders_l moduli_l i PreH13 (by omega)
  dump_pre_spatial
  omega

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure : chinese_remainder_theorem_partial_solve_wit_4_pure := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure
  right
  intro moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 moduli_pre remainders_pre n_pre moduli_l remainders_l result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_proof_manual
