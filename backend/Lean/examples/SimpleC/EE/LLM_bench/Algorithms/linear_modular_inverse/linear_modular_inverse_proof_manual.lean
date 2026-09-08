import SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_goal
import SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open linear_modular_inverse_lib

theorem proof_of_linear_modular_inverse_entail_wit_1 : linear_modular_inverse_entail_wit_1 := by
  pre_process
  all_goals
    have hpref : ModularInversePrefix p_pre 2 [1] := by
      constructor
      · rfl
      · intro index hi
        have hindex : index = 1 := by omega
        subst index
        change CanonicalModularInverse p_pre 1 1
        refine ⟨⟨by omega, by omega⟩, ⟨by decide, by omega⟩, 0, ?_⟩
        simp [Znth]
    Exists ([1] : List Int)
    have hs : ((inverse_pre + 1 * sizeof(INT)) # Int |-> (1 : Int)) |--
        naive_C_Rules.IntArray.seg inverse_pre 1 2 ([1] : List Int) :=
      naive_C_Rules.IntArray.seg_single inverse_pre 1 (1 : Int)
    sep_apply hs
    entailer!

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_1 : linear_modular_inverse_entail_wit_2_split_goal_1 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_2 : linear_modular_inverse_entail_wit_2_split_goal_2 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_3 : linear_modular_inverse_entail_wit_2_split_goal_3 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_4 : linear_modular_inverse_entail_wit_2_split_goal_4 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_5 : linear_modular_inverse_entail_wit_2_split_goal_5 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_6 : linear_modular_inverse_entail_wit_2_split_goal_6 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_7 : linear_modular_inverse_entail_wit_2_split_goal_7 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_8 : linear_modular_inverse_entail_wit_2_split_goal_8 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_9 : linear_modular_inverse_entail_wit_2_split_goal_9 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2_split_goal_10 : linear_modular_inverse_entail_wit_2_split_goal_10 := by
  pre_process
  all_goals
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH2 (by omega)
    have hv := (PreH7.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hprod := linear_inverse_product_bound__recurrence_core p_pre
      (p_pre - Z.div p_pre i) (Znth (Z.modulo p_pre i-1) values_2 0) (by omega) hf.2.2.2 hv
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [zdiv_equiv p_pre i (by omega) (by omega), rem_eq_mod p_pre i (by omega) (by omega)]
    first | omega | (simp only [INT_MAX, INT_MIN] at *; omega) | grind

theorem proof_of_linear_modular_inverse_entail_wit_2 : linear_modular_inverse_entail_wit_2 := by
  unfold linear_modular_inverse_entail_wit_2
  right
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_1 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_2 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_3 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_4 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_5 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_6 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_7 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_8 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_9 p_pre values_2 i) <;> assumption)
      | (apply (proof_of_linear_modular_inverse_entail_wit_2_split_goal_10 p_pre values_2 i) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)

theorem proof_of_linear_modular_inverse_entail_wit_3_split_goal_1 : linear_modular_inverse_entail_wit_3_split_goal_1 := by
  pre_process
  all_goals
    have hp0 : 0 ≤ p_pre := by have := PreH1.1; omega
    have hi0 : 0 < i := by omega
    have hq := zdiv_equiv p_pre i hp0 hi0
    have hr := rem_eq_mod p_pre i hp0 hi0
    rw [hq] at PreH6
    rw [hr] at PreH7
    subst quotient remainder
    rw [← PreH8]
    have hf := linear_inverse_division_facts__recurrence_core p_pre i PreH1 (by omega)
    have hv := (PreH18.2 (Z.modulo p_pre i) (by have := hf.2.2.1; omega)).2.1
    have hpositive := Int.mul_pos hf.2.2.2.1 hv.1
    have hnonneg := Int.le_of_lt hpositive
    simp only [hq, hr, rem_eq_mod _ p_pre hnonneg (by omega)]
    exact linear_inverse_prefix_extend__recurrence_core p_pre i (Z.div p_pre i)
      (Z.modulo p_pre i) values_2 PreH1 (by omega) rfl rfl PreH18

theorem proof_of_linear_modular_inverse_entail_wit_3 : linear_modular_inverse_entail_wit_3 := by
  unfold linear_modular_inverse_entail_wit_3
  right
  pre_process
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_linear_modular_inverse_entail_wit_3_split_goal_1 p_pre values_2 i quotient remainder) <;> assumption)
      | (simp only [INT_MAX, INT_MIN] at *; omega)

theorem proof_of_linear_modular_inverse_return_wit_1 : linear_modular_inverse_return_wit_1 := by
  unfold linear_modular_inverse_return_wit_1
  right
  pre_process
  have hi : i = p_pre := by omega
  subst i
  Exists values_2
  entailer!

end SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_proof_manual
