import Algorithms.extended_chinese_remainder_theorem.lean.groundtruth.extended_chinese_remainder_theorem_goal
import Algorithms.extended_chinese_remainder_theorem.lean.groundtruth.extended_chinese_remainder_theorem_proof_auto
import AUXLib.NumberTheory
import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.extended_chinese_remainder_theorem.lean.groundtruth.extended_chinese_remainder_theorem_proof_manual

open Algorithms.extended_chinese_remainder_theorem.lean

open AUXLib

theorem extended_crt_index_bounds__machine_bounds (residues moduli : List Int) (n index : Int)
    (hi : ExtendedCRTInputs residues moduli n) (hx : 0 ≤ index ∧ index < n) :
    (0 < Znth index moduli 0 ∧ Znth index moduli 0 ≤ 2147483647) ∧
    (0 ≤ Znth index residues 0 ∧ Znth index residues 0 < Znth index moduli 0) := hi.2.2.2 index hx

theorem positive_gcd_quotient_bounds__machine_bounds (current_modulus modulus gcd : Int)
    (hm : 0 < modulus ∧ modulus ≤ 2147483647) (hg : gcd = Z.gcd current_modulus modulus)
    (hgp : 0 < gcd) : 0 < Z.quot modulus gcd ∧ Z.quot modulus gcd ≤ 2147483647 := by
  obtain ⟨q, hq⟩ : Z.divide gcd modulus := by rw [hg]; exact Z.gcd_divide_r current_modulus modulus
  have hqp : 0 < q := by
    exact Int.pos_of_mul_pos_left (show 0 < q*gcd by omega) hgp
  have hle := Int.mul_le_mul_of_nonneg_left (show 1 ≤ gcd by omega) (Int.le_of_lt hqp)
  rw [hq, Z.quot_mul q gcd (by omega)]
  simp only [Int.mul_one] at hle
  omega

theorem signed_difference_division_bounds__machine_bounds (residue answer divisor : Int)
    (hr : 0 ≤ residue ∧ residue ≤ 2147483647) (ha : 0 ≤ answer ∧ answer ≤ 2147483647)
    (hd : 0 < divisor) : -2147483648 < Z.quot (residue-answer) divisor ∧
    Z.quot (residue-answer) divisor ≤ 2147483647 := by
  have hl := Int.mul_le_mul_of_nonpos_right (show 1 ≤ divisor by omega) (show (-2147483647 : Int) ≤ 0 by decide)
  have hu := Int.mul_le_mul_of_nonneg_right (show 1 ≤ divisor by omega) (show (0 : Int) ≤ 2147483647 by decide)
  have hlow := Z.quot_le_lower_bound (residue-answer) divisor (-2147483647) hd (by omega)
  have hupp := Z.quot_le_upper_bound (residue-answer) divisor 2147483647 hd (by omega)
  omega

theorem bounded_merge_arithmetic__machine_bounds (answer lcm multiplier reduced_modulus : Int)
    (ha : 0 ≤ answer ∧ answer < lcm) (hm : 0 ≤ multiplier ∧ multiplier < reduced_modulus)
    (hl : 0 < lcm) (hp : lcm*reduced_modulus ≤ 2147483647) :
    multiplier*lcm ≤ 2147483647 ∧ -2147483648 ≤ multiplier*lcm ∧
    answer+multiplier*lcm ≤ 2147483647 ∧ -2147483648 ≤ answer+multiplier*lcm := by
  have hn := Int.mul_nonneg hm.1 (Int.le_of_lt hl)
  have hu := Int.mul_le_mul_of_nonneg_right (show multiplier+1 ≤ reduced_modulus by omega) (Int.le_of_lt hl)
  simp only [Int.add_mul, Int.one_mul] at hu
  rw [Int.mul_comm reduced_modulus lcm] at hu
  omega

theorem crt_prefix_meaning_one__prefix_boundaries (residues moduli : List Int) (n : Int)
    (hi : ExtendedCRTInputs residues moduli n) (hn : 1 ≤ n) :
    CRTPrefixMeaning residues moduli 1 (Znth 0 residues 0) (Znth 0 moduli 0) := by
  have hrlen := hi.2.1
  have hmlen := hi.2.2.1
  have hz := hi.2.2.2 0 (by omega)
  cases residues with
  | nil => simp [Zlength] at hrlen; omega
  | cons r rs =>
    cases moduli with
    | nil => simp [Zlength] at hmlen; omega
    | cons m ms =>
      simp only [Znth, Int.toNat_zero, List.getD_cons_zero] at hz ⊢
      refine ⟨?_, ?_⟩
      · change m = Z.lcm 1 m
        exact (Z.lcm_1_l_nonneg m (by omega)).symm
      · intro index hx
        have hidx : index = 0 := by omega
        subst index
        exact ⟨0, by simp [Znth]⟩

theorem crt_prefix_meaning_to_result__prefix_boundaries (residues moduli : List Int)
    (n i answer combined_modulus : Int) (he : i = n) (ha : 0 ≤ answer ∧ answer < combined_modulus)
    (hp : CRTPrefixMeaning residues moduli i answer combined_modulus) :
    ExtendedCRTSystemResult residues moduli n answer combined_modulus := by
  subst i
  exact ⟨hp.1, ha, hp.2⟩

theorem quot_div_of_divide_pos__merge_transition (numerator denominator : Int)
    (hd : 0 < denominator) (hdiv : Z.divide denominator numerator) :
    Z.quot numerator denominator = Z.div numerator denominator := by
  obtain ⟨q, hq⟩ := hdiv
  rw [hq, Z.quot_mul q denominator (by omega)]
  exact (Int.mul_fdiv_cancel q (by omega)).symm

theorem firstn_succ_nth__merge_transition {A : Type} (l : List A) (n : Nat) (default : A)
    (hn : n < l.length) : l.take (n+1) = l.take n ++ [l.getD n default] := by
  rw [List.take_succ_eq_append_getElem hn]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

theorem fold_left_lcm_all_divide__merge_transition (values : List Int) (accumulator difference : Int)
    (ha : Z.divide accumulator difference)
    (hall : ∀ value, value ∈ values → Z.divide value difference) :
    Z.divide (values.foldl Z.lcm accumulator) difference := by
  induction values generalizing accumulator with
  | nil => exact ha
  | cons v vs ih =>
    apply ih (Z.lcm accumulator v) (Z.lcm_least accumulator v difference ha (hall v (by simp)))
    intro other ho
    exact hall other (List.mem_cons_of_mem _ ho)

theorem fold_left_lcm_preserves_divide__merge_transition (values : List Int) (accumulator divisor : Int)
    (hd : Z.divide divisor accumulator) : Z.divide divisor (values.foldl Z.lcm accumulator) := by
  induction values generalizing accumulator with
  | nil => exact hd
  | cons v vs ih =>
    apply ih
    apply (Z.divide_iff_dvd _ _).mpr
    exact Int.dvd_trans ((Z.divide_iff_dvd _ _).mp hd) ((Z.divide_iff_dvd _ _).mp (Z.divide_lcm_l accumulator v))

theorem fold_left_lcm_in_divides__merge_transition (values : List Int) (accumulator value : Int)
    (hm : value ∈ values) : Z.divide value (values.foldl Z.lcm accumulator) := by
  induction values generalizing accumulator with
  | nil => simp at hm
  | cons v vs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact fold_left_lcm_preserves_divide__merge_transition vs (Z.lcm accumulator value) value (Z.divide_lcm_r accumulator value)
    · exact ih (Z.lcm accumulator v) hm

theorem crt_lcm_prefix_multiple__merge_transition (moduli : List Int) (count index : Int)
    (hi : 0 ≤ index ∧ index < count) (hc : count ≤ Zlength moduli) :
    Z.divide (Znth index moduli 0) (CRTLCMPrefix moduli count) := by
  apply fold_left_lcm_in_divides__merge_transition
  apply List.mem_take_iff_getElem.mpr
  have hlen : index.toNat < moduli.length := by simp only [Zlength, Int.ofNat_eq_coe] at hc; omega
  refine ⟨index.toNat, by simp only [Zlength, Int.ofNat_eq_coe] at hc; omega, ?_⟩
  simp [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]

theorem crt_prefix_solution_congruent_lcm__merge_transition (residues moduli : List Int)
    (count answer combined solution : Int) (hc : 0 ≤ count)
    (hp : CRTPrefixMeaning residues moduli count answer combined)
    (hs : CRTAllCongruences residues moduli count solution) : Z.divide combined (solution-answer) := by
  rw [hp.1]
  apply fold_left_lcm_all_divide__merge_transition
  · exact ⟨solution-answer, by omega⟩
  · intro modulus hm
    obtain ⟨k, hk, he⟩ := List.mem_take_iff_getElem.mp hm
    have hkr : 0 ≤ (k : Int) ∧ (k : Int) < count := by omega
    have hmod : Znth (k : Int) moduli 0 = modulus := by
      simpa [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < moduli.length by omega)] using he
    obtain ⟨qa, ha⟩ := hp.2 (k : Int) hkr
    obtain ⟨qs, hsol⟩ := hs (k : Int) hkr
    rw [hmod] at ha hsol
    exact ⟨qs-qa, by grind⟩

theorem crt_merge_difference_divisible__merge_transition (residues moduli : List Int)
    (n index answer combined : Int) (hc : ExtendedCRTSystemCompatible residues moduli n)
    (hp : CRTPrefixMeaning residues moduli index answer combined) (hi : 0 ≤ index ∧ index < n) :
    Z.divide (Z.gcd combined (Znth index moduli 0)) (Znth index residues 0-answer) := by
  obtain ⟨solution, hs⟩ := hc
  have hsp : CRTAllCongruences residues moduli index solution := by
    intro old ho
    exact hs old (by omega)
  obtain ⟨qp, hqp⟩ := crt_prefix_solution_congruent_lcm__merge_transition residues moduli index answer combined solution hi.1 hp hsp
  obtain ⟨qn, hqn⟩ := hs index hi
  obtain ⟨qc, hqc⟩ := Z.gcd_divide_l combined (Znth index moduli 0)
  obtain ⟨qm, hqm⟩ := Z.gcd_divide_r combined (Znth index moduli 0)
  exact ⟨qc*qp-qm*qn, by grind⟩

theorem reduced_merge_equation_from_bezout__merge_transition
    (current_answer current_modulus next_residue next_modulus gcd x_coefficient y_coefficient normalized quotient : Int)
    (hg : gcd = Z.gcd current_modulus next_modulus) (hgp : 0 < gcd)
    (hd : Z.divide gcd (next_residue-current_answer))
    (hb : current_modulus*x_coefficient+next_modulus*y_coefficient = gcd)
    (hn : x_coefficient*Z.div (next_residue-current_answer) gcd = normalized+Z.div next_modulus gcd*quotient) :
    CRTReducedMergeEquation current_answer current_modulus next_residue next_modulus normalized := by
  obtain ⟨cq, hc⟩ : Z.divide gcd current_modulus := by rw [hg]; exact Z.gcd_divide_l current_modulus next_modulus
  obtain ⟨nq, hnext⟩ : Z.divide gcd next_modulus := by rw [hg]; exact Z.gcd_divide_r current_modulus next_modulus
  obtain ⟨dq, hdiff⟩ := hd
  have hcd : Z.div current_modulus gcd = cq := by rw [hc]; exact Int.mul_fdiv_cancel cq (by omega)
  have hnd : Z.div next_modulus gcd = nq := by rw [hnext]; exact Int.mul_fdiv_cancel nq (by omega)
  have hdd : Z.div (next_residue-current_answer) gcd = dq := by rw [hdiff]; exact Int.mul_fdiv_cancel dq (by omega)
  have hunit : cq*x_coefficient+nq*y_coefficient = 1 := by
    apply Int.eq_of_mul_eq_mul_right (a := gcd) (by omega)
    grind
  unfold CRTReducedMergeEquation
  rw [← hg]
  refine ⟨y_coefficient*dq+cq*quotient, ?_⟩
  rw [hcd, hnd, hdd]
  rw [hnd, hdd] at hn
  grind

theorem crt_lcm_prefix_step__merge_transition (residues moduli : List Int)
    (n index answer combined gcd reduced : Int) (hi : ExtendedCRTInputs residues moduli n)
    (hx : 0 ≤ index ∧ index < n) (hp : 0 < combined)
    (hprefix : CRTPrefixMeaning residues moduli index answer combined)
    (hg : gcd = Z.gcd combined (Znth index moduli 0)) (hgp : 0 < gcd)
    (hr : reduced = Z.div (Znth index moduli 0) gcd) :
    CRTLCMPrefix moduli (index+1) = combined*reduced := by
  have hlen := hi.2.2.1
  have hm := (hi.2.2.2 index hx).1.1
  have hnat : index.toNat < moduli.length := by simp only [Zlength, Int.ofNat_eq_coe] at hlen; omega
  unfold CRTLCMPrefix
  rw [show (index+1).toNat = index.toNat+1 by omega,
    firstn_succ_nth__merge_transition moduli index.toNat 0 hnat, List.foldl_append]
  change Z.lcm (CRTLCMPrefix moduli index) (Znth index moduli 0) = combined*reduced
  rw [← hprefix.1]
  unfold Z.lcm
  rw [← hg, ← hr]
  apply (Z.abs_eq_iff _).mpr
  apply Int.mul_nonneg (Int.le_of_lt hp)
  rw [hr]
  exact Int.fdiv_nonneg (Int.le_of_lt hm) (Int.le_of_lt hgp)

theorem crt_prefix_meaning_merge__merge_transition (residues moduli : List Int)
    (n index answer combined gcd reduced multiplier : Int)
    (hi : ExtendedCRTInputs residues moduli n) (hc : ExtendedCRTSystemCompatible residues moduli n)
    (hx : 0 ≤ index ∧ index < n) (hp : 0 < combined)
    (hprefix : CRTPrefixMeaning residues moduli index answer combined)
    (hg : gcd = Z.gcd combined (Znth index moduli 0)) (hgp : 0 < gcd)
    (hr : reduced = Z.div (Znth index moduli 0) gcd) (hm : 0 ≤ multiplier ∧ multiplier < reduced)
    (hmerge : CRTReducedMergeEquation answer combined (Znth index residues 0) (Znth index moduli 0) multiplier) :
    CRTPrefixMeaning residues moduli (index+1) (answer+multiplier*combined) (combined*reduced) := by
  refine ⟨(crt_lcm_prefix_step__merge_transition residues moduli n index answer combined gcd reduced hi hx hp hprefix hg hgp hr).symm, ?_⟩
  intro old ho
  by_cases hold : old < index
  · obtain ⟨qo, hqo⟩ := hprefix.2 old (by omega)
    obtain ⟨qcomb, hcomb⟩ := crt_lcm_prefix_multiple__merge_transition moduli index old (by omega) (by have := hi.2.2.1; omega)
    have hpre := hprefix.1
    exact ⟨qo+multiplier*qcomb, by grind⟩
  · have heq : old = index := by omega
    subst old
    obtain ⟨cq, hcq⟩ : Z.divide gcd combined := by rw [hg]; exact Z.gcd_divide_l combined (Znth index moduli 0)
    obtain ⟨mq, hmq⟩ : Z.divide gcd (Znth index moduli 0) := by rw [hg]; exact Z.gcd_divide_r combined (Znth index moduli 0)
    obtain ⟨dq, hdq⟩ : Z.divide gcd (Znth index residues 0-answer) := by
      rw [hg]; exact crt_merge_difference_divisible__merge_transition residues moduli n index answer combined hc hprefix hx
    have hcd : Z.div combined gcd = cq := by rw [hcq]; exact Int.mul_fdiv_cancel cq (by omega)
    have hmd : Z.div (Znth index moduli 0) gcd = mq := by rw [hmq]; exact Int.mul_fdiv_cancel mq (by omega)
    have hdd : Z.div (Znth index residues 0-answer) gcd = dq := by rw [hdq]; exact Int.mul_fdiv_cancel dq (by omega)
    unfold CRTReducedMergeEquation at hmerge
    rw [← hg] at hmerge
    obtain ⟨adjustment, ha⟩ := hmerge
    rw [hcd, hmd, hdd] at ha
    exact ⟨-adjustment, by grind⟩

theorem bezout_coefficient_strict__gcd_branch_setup (lcm modulus gcd x y : Int)
    (hm : 0 < modulus) (hg : gcd = Z.gcd lcm modulus) (hgp : 0 < gcd)
    (hn : Z.rem lcm modulus ≠ 0) (hb : lcm*x+modulus*y = gcd)
    (ha : Z.abs x ≤ Z.quot modulus gcd) : -Z.quot modulus gcd < x ∧ x < Z.quot modulus gcd := by
  obtain ⟨lq, hlq⟩ : Z.divide gcd lcm := by rw [hg]; exact Z.gcd_divide_l lcm modulus
  obtain ⟨mq, hmq⟩ : Z.divide gcd modulus := by rw [hg]; exact Z.gcd_divide_r lcm modulus
  have hquot : Z.quot modulus gcd = mq := by rw [hmq, Z.quot_mul mq gcd (by omega)]
  have hmqpos : 0 < mq := Int.pos_of_mul_pos_left (show 0 < mq*gcd by omega) hgp
  have hu : lq*x+mq*y = 1 := by
    apply Int.eq_of_mul_eq_mul_right (a := gcd) (by omega)
    grind
  have hmne : mq ≠ 1 := by
    intro he
    apply hn
    have hmg : modulus = gcd := by simpa only [he, Int.one_mul] using hmq
    rw [hmg]
    exact (Z.rem_divide lcm gcd (by omega)).mpr ⟨lq, hlq⟩
  rw [hquot] at ha ⊢
  have hab := (Z.abs_le_iff x mq).mp ha
  have hneg : x ≠ -mq := by
    intro he
    have hd : mq ∣ 1 := ⟨y-lq, by grind⟩
    have := Int.le_of_dvd (show (0 : Int) < 1 by decide) hd
    omega
  have hpos : x ≠ mq := by
    intro he
    have hd : mq ∣ 1 := ⟨lq+y, by grind⟩
    have := Int.le_of_dvd (show (0 : Int) < 1 by decide) hd
    omega
  omega


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.extended_chinese_remainder_theorem.lean.groundtruth.extended_chinese_remainder_theorem_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Use the original generated residual branch and SL preprocessing. Goal_apply
-- requires explicit arguments in Lean; pure split results also need the
-- dump_spatial_left bridge from entailments to propositions.

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_safety_wit_7_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH1 ⟨PreH4, PreH6⟩
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_safety_wit_7_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH1 ⟨PreH4, PreH6⟩
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7 := by
  unfold extended_chinese_remainder_theorem_safety_wit_7
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_safety_wit_10_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_safety_wit_10_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_10 : extended_chinese_remainder_theorem_safety_wit_10 := by
  unfold extended_chinese_remainder_theorem_safety_wit_10
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_safety_wit_11_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_safety_wit_11_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_11 : extended_chinese_remainder_theorem_safety_wit_11 := by
  unfold extended_chinese_remainder_theorem_safety_wit_11
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_1_split_goal_1
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH1.1

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_1
  right
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_1
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  exact crt_prefix_meaning_one__prefix_boundaries residue_values modulus_values n_pre PreH2 PreH1

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_2
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_3
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_4
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_5
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2 : extended_chinese_remainder_theorem_entail_wit_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2
  right
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hs := bezout_coefficient_strict__gcd_branch_setup lcm (Znth i modulus_values 0) retval x_callee_v y_callee_v hb.1.1 PreH2 PreH1 PreH5 PreH3 PreH4
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hs := bezout_coefficient_strict__gcd_branch_setup lcm (Znth i modulus_values 0) retval x_callee_v y_callee_v hb.1.1 PreH2 PreH1 PreH5 PreH3 PreH4
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hs := PreH9.2 i (by omega)
  have hp := PreH16.1
  change retval = Z.gcd lcm (Znth i modulus_values 0) at PreH2
  rw [← hp, ← PreH2] at hs
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH3

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH2

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1
  right
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hs := PreH10.2 i (by omega)
  have hp := PreH17.1
  change retval = Z.gcd lcm (Znth i modulus_values 0) at PreH2
  rw [← hp, ← PreH2] at hs
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  simpa only [PreH6] using PreH3

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH2

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2
  right
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hd : Z.divide gcd (Znth i residue_values 0-answer) := by
    rw [PreH14]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm PreH4 PreH13 ⟨PreH6, PreH8⟩
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) gcd PreH15 hd
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm
  obtain ⟨hb, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have hr : reduced_modulus = Z.div (Znth i modulus_values 0) gcd := PreH17.trans hmod
  apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) gcd x y (retval+reduced_modulus) (q-1) PreH14 PreH15 hd PreH16
  rw [← hr]
  grind

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hr := PreH17.trans (quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm)
  have hp := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm gcd reduced_modulus PreH3 ⟨PreH6, PreH8⟩ PreH11 PreH13 PreH14 PreH15 hr
  have hs := (PreH5.1 (i+1) (by omega)).2
  rw [hp] at hs
  exact hs

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hb := PreH2.1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  exact replace_Znth_Znth i residue_values 0

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1 : extended_chinese_remainder_theorem_entail_wit_4_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1
  right
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hd : Z.divide gcd (Znth i residue_values 0-answer) := by
    rw [PreH14]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm PreH4 PreH13 ⟨PreH6, PreH8⟩
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) gcd PreH15 hd
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm
  obtain ⟨hb, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have hr : reduced_modulus = Z.div (Znth i modulus_values 0) gcd := PreH17.trans hmod
  apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) gcd x y retval q PreH14 PreH15 hd PreH16
  rw [← hr]
  grind

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hr := PreH17.trans (quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm)
  have hp := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm gcd reduced_modulus PreH3 ⟨PreH6, PreH8⟩ PreH11 PreH13 PreH14 PreH15 hr
  have hs := (PreH5.1 (i+1) (by omega)).2
  rw [hp] at hs
  exact hs

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hb := PreH2.1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  exact replace_Znth_Znth i residue_values 0

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2 : extended_chinese_remainder_theorem_entail_wit_4_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2
  right
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_5_split_goal_1
  intro n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH11]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hr := PreH13.trans (quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH12 hm)
  exact crt_prefix_meaning_merge__merge_transition residue_values modulus_values n_pre i answer lcm gcd reduced_modulus x PreH1 PreH2 (by omega) PreH8 PreH10 PreH11 PreH12 hr ⟨PreH16, PreH17⟩ PreH20

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_5_split_goal_2
  intro n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  have hu := Int.mul_le_mul_of_nonneg_right (show x+1 ≤ reduced_modulus by omega) (Int.le_of_lt PreH8)
  simp only [Int.add_mul, Int.one_mul] at hu
  rw [Int.mul_comm reduced_modulus lcm] at hu
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_5 : extended_chinese_remainder_theorem_entail_wit_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_5
  right
  intro n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1 : extended_chinese_remainder_theorem_return_wit_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_return_wit_1_split_goal_1
  intro n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  try simp only [INT_MAX, INT_MIN] at *
  exact crt_prefix_meaning_to_result__prefix_boundaries residue_values modulus_values n_pre i answer lcm (by omega) ⟨PreH7, PreH8⟩ PreH11

theorem proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1 := by
  unfold extended_chinese_remainder_theorem_return_wit_1
  right
  intro n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1 n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | exact (proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1 n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH9 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH9 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_4_pure
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | trivial

end Algorithms.extended_chinese_remainder_theorem.lean.groundtruth.extended_chinese_remainder_theorem_proof_manual
