import Algorithms.linear_modular_inverse.lean.groundtruth.linear_modular_inverse_goal
import Algorithms.linear_modular_inverse.lean.groundtruth.linear_modular_inverse_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.linear_modular_inverse.lean.groundtruth.linear_modular_inverse_proof_manual

open Algorithms.linear_modular_inverse.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

theorem linear_inverse_division_facts__recurrence_core (p i : Int)
    (hp : PrimeForLinearInverse p) (hi : 2 ≤ i ∧ i < p) :
    p = Z.div p i * i + Z.modulo p i ∧ 1 ≤ Z.div p i ∧
    (1 ≤ Z.modulo p i ∧ Z.modulo p i < i) ∧ (0 < p - Z.div p i ∧ p - Z.div p i < p) := by
  have hd := Int.fdiv_mul_add_fmod p i
  have hr0 := Int.fmod_nonneg_of_pos p (show 0 < i by omega)
  have hr1 := Int.fmod_lt_of_pos p (show 0 < i by omega)
  have hrn := hp.2 i hi
  have hq0 := Int.fdiv_nonneg (show 0 ≤ p by have := hp.1; omega) (show 0 ≤ i by omega)
  unfold Z.div Z.modulo at *
  have hq1 : 1 ≤ p.fdiv i := by
    by_cases h : 1 ≤ p.fdiv i
    · exact h
    · have hzero : p.fdiv i = 0 := by omega
      simp [hzero] at hd
      omega
  have hqp : p.fdiv i < p := by
    have hmul := Int.mul_le_mul_of_nonneg_left (show 1 ≤ i by omega) hq0
    simp only [Int.mul_one] at hmul
    omega
  exact ⟨hd.symm, hq1, by omega, by omega⟩

theorem linear_inverse_product_bound__recurrence_core (p a b : Int)
    (hp : 2 ≤ p ∧ p ≤ 46340) (ha : 0 < a ∧ a < p) (hb : 0 < b ∧ b < p) :
    a * b ≤ 2147483647 := by
  have h1 := Int.mul_le_mul_of_nonneg_right (show a ≤ 46340 by omega) (show 0 ≤ b by omega)
  have h2 := Int.mul_le_mul_of_nonneg_left (show b ≤ 46340 by omega) (show (0 : Int) ≤ 46340 by decide)
  omega

theorem linear_inverse_prefix_extend__recurrence_core (p i q r : Int) (values : List Int)
    (hp : PrimeForLinearInverse p) (hi : 2 ≤ i ∧ i < p)
    (hq : q = Z.div p i) (hr : r = Z.modulo p i) (hpre : ModularInversePrefix p i values) :
    ModularInversePrefix p (i + 1)
      (values ++ [Z.modulo ((p-q) * Znth (r-1) values 0) p]) := by
  subst q r
  obtain ⟨hd, hq1, hrem, hdiff⟩ := linear_inverse_division_facts__recurrence_core p i hp hi
  obtain ⟨hlen, hpre⟩ := hpre
  obtain ⟨_, hv, c, hc⟩ := hpre (Z.modulo p i) hrem
  constructor
  · rw [Zlength_app, hlen]
    simp [Zlength]
  · intro index hindex
    by_cases hlt : index < i
    · have hi0 : 0 ≤ index - 1 := by omega
      have hin : (index-1).toNat < values.length := by
        have := (Int.toNat_lt_toNat (show 0 < Zlength values by omega)).2 (show index-1 < Zlength values by omega)
        simpa [Zlength] using this
      have heq : Znth (index-1) (values ++ [Z.modulo ((p-Z.div p i) * Znth (Z.modulo p i-1) values 0) p]) 0 =
          Znth (index-1) values 0 := by
        simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_append_left hin]
      rw [heq]
      exact hpre index ⟨hindex.1, hlt⟩
    · have hieq : index = i := by omega
      subst index
      rw [app_Znth2 0 values _ (i-1) (by omega), hlen]
      simp only [Int.sub_self, Znth0_cons]
      let value := Znth (Z.modulo p i - 1) values 0
      let raw := (p - Z.div p i) * value
      have hp0 : 0 < p := by have := hp.1; omega
      have hraw : raw = p * Z.div raw p + Z.modulo raw p := (Int.mul_fdiv_add_fmod raw p).symm
      have hm0 : 0 ≤ Z.modulo raw p := Int.fmod_nonneg_of_pos raw hp0
      have hm1 : Z.modulo raw p < p := Int.fmod_lt_of_pos raw hp0
      have hinv : i * Z.modulo raw p + p * (c - i*value + value + i*Z.div raw p) = 1 := by
        change Z.modulo p i * value + p*c = 1 at hc
        have hbez : i*raw + p*(c-i*value+value) = 1 := by dsimp [raw]; grind
        grind
      have hnz : Z.modulo raw p ≠ 0 := by
        intro hz
        have hmult : p * (c-i*value+value+i*Z.div raw p) = 1 := by rw [hz, Int.mul_zero, Int.zero_add] at hinv; exact hinv
        have hmod := congrArg (fun x : Int => x.fmod p) hmult
        simp only [Int.mul_fmod_right, Int.fmod_eq_of_lt (show (0 : Int) ≤ 1 by decide) (show 1 < p by have := hp.1; omega)] at hmod
        contradiction
      change CanonicalModularInverse p i (Z.modulo raw p)
      exact ⟨by omega, ⟨by omega, hm1⟩, _, hinv⟩

end ProofSupport

open ProofSupport
open Algorithms.linear_modular_inverse.lean.groundtruth.linear_modular_inverse_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.linear_modular_inverse.lean.groundtruth.linear_modular_inverse_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open ProofSupport

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

end Algorithms.linear_modular_inverse.lean.groundtruth.linear_modular_inverse_proof_manual
