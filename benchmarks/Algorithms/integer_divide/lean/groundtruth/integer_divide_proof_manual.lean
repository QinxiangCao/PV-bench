import Algorithms.integer_divide.lean.groundtruth.integer_divide_goal
import Algorithms.integer_divide.lean.groundtruth.integer_divide_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.Prime

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.integer_divide.lean.groundtruth.integer_divide_proof_manual

open Algorithms.integer_divide.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib
export AUXLib.Prime (prime prime_alt prime_ge_2)

/-- Coq `Sorting.Sorted.HdRel`: only the relation to the first list element. -/
theorem prime_product_exceeds_length__progress_transitions (factors : List Int)
    (h : Forall prime factors) : Zlength factors < factors.foldr (· * ·) 1 := by
  induction h with
  | nil => simp [Zlength]
  | @cons factor factors hf hfs ih =>
    simp only [Zlength_cons, List.foldr_cons]
    have hf2 := prime_ge_2 factor hf
    have hl : 0 ≤ Zlength factors := by simp [Zlength]
    have hm := Int.mul_le_mul_of_nonneg_right hf2 (show 0 ≤ factors.foldr (· * ·) 1 by omega)
    omega

theorem fold_right_mul_snoc__progress_transitions (factors : List Int) (factor : Int) :
    (factors ++ [factor]).foldr (· * ·) 1 = factors.foldr (· * ·) 1 * factor := by
  induction factors with
  | nil => simp
  | cons head tail ih => simp only [List.cons_append, List.foldr_cons, ih, Int.mul_assoc]

theorem sorted_snoc_le__progress_transitions (factors : List Int) (factor : Int)
    (hs : Sorted (· ≤ ·) factors) (hb : Forall (fun x => x ≤ factor) factors) :
    Sorted (· ≤ ·) (factors ++ [factor]) := by
  induction hs with
  | Sorted_nil => exact .Sorted_cons factor [] .Sorted_nil .HdRel_nil
  | Sorted_cons head tail ht hh ih =>
    cases hb with
    | cons hhead htail =>
      apply Sorted.Sorted_cons head (tail ++ [factor]) (ih htail)
      cases tail with
      | nil => exact .HdRel_cons factor [] hhead
      | cons next rest =>
        cases hh with
        | HdRel_cons _ _ h => exact .HdRel_cons next (rest ++ [factor]) h

theorem factorization_progress_room__progress_transitions
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hc : 2 ≤ candidate) (hr : candidate ≤ remaining)
    (hp : FactorizationProgress original factors remaining candidate) :
    Zlength factors + 1 < original := by
  obtain ⟨hprod, hprime, _⟩ := hp
  have hb := prime_product_exceeds_length__progress_transitions factors hprime
  have hl : 0 ≤ Zlength factors := by simp [Zlength]
  have hm := Int.mul_le_mul_of_nonneg_left (show 2 ≤ remaining by omega)
    (show 0 ≤ factors.foldr (· * ·) 1 by omega)
  omega

theorem factorization_progress_extract__progress_transitions
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hr : 1 ≤ remaining) (hc : 2 ≤ candidate) (hcr : candidate ≤ remaining)
    (hmod : Z.rem remaining candidate = 0)
    (hp : FactorizationProgress original factors remaining candidate) :
    FactorizationProgress original (factors ++ [candidate])
      (Z.quot remaining candidate) candidate ∧
    (Z.quot remaining candidate = 1 ∨ candidate ≤ Z.quot remaining candidate) := by
  obtain ⟨hprod, hprimes, hsorted, hbounds, hexc⟩ := hp
  have hdiv : remaining = candidate * Z.quot remaining candidate := by
    have h := Z.quot_rem remaining candidate (by omega)
    omega
  have hprime : prime candidate := by
    apply (prime_alt candidate).mp
    refine ⟨by omega, ?_⟩
    intro d hd hdvd
    apply hexc d (by omega)
    obtain ⟨q, hq⟩ := hdvd
    exact ⟨q * Z.quot remaining candidate, by grind⟩
  have hqpos : 1 ≤ Z.quot remaining candidate :=
    Z.quot_le_lower_bound remaining candidate 1 (by omega) (by omega)
  have hcases : Z.quot remaining candidate = 1 ∨ candidate ≤ Z.quot remaining candidate := by
    by_cases h1 : Z.quot remaining candidate = 1
    · exact .inl h1
    · right
      apply Classical.byContradiction
      intro hlt
      apply hexc (Z.quot remaining candidate) (by omega)
      exact ⟨candidate, hdiv⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hcases⟩
  · rw [fold_right_mul_snoc__progress_transitions]
    grind
  · apply Forall.iff_forall_mem.mpr
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hprimes.mem hq
    · have heq := List.mem_singleton.mp hq
      subst q
      exact hprime
  · exact sorted_snoc_le__progress_transitions factors candidate hsorted hbounds
  · apply Forall.iff_forall_mem.mpr
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hbounds.mem hq
    · have := List.mem_singleton.mp hq; omega
  · intro d hd hdvd
    apply hexc d hd
    obtain ⟨q, hq⟩ := hdvd
    exact ⟨candidate * q, by grind⟩

theorem factorization_progress_advance__progress_transitions
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hc : 2 ≤ candidate) (hm : Z.rem remaining candidate ≠ 0)
    (hp : FactorizationProgress original factors remaining candidate) :
    FactorizationProgress original factors remaining (candidate + 1) := by
  obtain ⟨hprod, hprimes, hs, hb, hexc⟩ := hp
  refine ⟨hprod, hprimes, hs, ?_, ?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro q hq
    have := hb.mem hq
    omega
  · intro d hd hdvd
    by_cases hlt : d < candidate
    · exact hexc d (by omega) hdvd
    · have heq : d = candidate := by omega
      subst d
      exact hm ((Z.rem_divide remaining candidate (by omega)).2 hdvd)

private theorem prime_mul_dvd {q a b : Int} (hq : prime q) (hd : q ∣ a * b) :
    q ∣ a ∨ q ∣ b := by
  by_cases hqa : q ∣ a
  · exact .inl hqa
  · right
    have hq2 := prime_ge_2 q hq
    have hgpos := Int.gcd_pos_of_ne_zero_left a (show q ≠ 0 by omega)
    have hgle := Int.gcd_le_left a (show 0 < q by omega)
    have hgd := Int.gcd_dvd_left q a
    have hgda := Int.gcd_dvd_right q a
    have hgne : (Int.gcd q a : Int) ≠ q := by
      intro heq
      exact hqa (heq ▸ hgda)
    have hg1 : Int.gcd q a = 1 := by
      apply Classical.byContradiction
      intro hn
      exact ((prime_alt q).mpr hq).2 (Int.gcd q a) (by omega) ((Z.divide_iff_dvd _ _).2 hgd)
    have hm := (Int.dvd_gcd_mul_iff_dvd_mul (k := q) (n := a) (m := b)).2 hd
    simpa [hg1] using hm

theorem prime_divides_factor_product_iff_in__final_result (q : Int) (factors : List Int)
    (hq : prime q) (hall : Forall prime factors) :
    Z.divide q (factors.foldr (· * ·) 1) ↔ q ∈ factors := by
  rw [Z.divide_iff_dvd]
  induction hall with
  | nil =>
    simp only [List.foldr_nil, List.not_mem_nil, iff_false]
    intro hd
    have := Int.le_of_dvd (show (0 : Int) < 1 by decide) hd
    have := prime_ge_2 q hq
    omega
  | @cons a factors ha hall ih =>
    simp only [List.foldr_cons, List.mem_cons]
    constructor
    · intro hd
      rcases prime_mul_dvd hq hd with hda | hdf
      · left
        have hq2 := prime_ge_2 q hq
        have ha2 := prime_ge_2 a ha
        have hle := Int.le_of_dvd (show 0 < a by omega) hda
        apply Classical.byContradiction
        intro hne
        exact ((prime_alt a).mpr ha).2 q (by omega) ((Z.divide_iff_dvd _ _).2 hda)
      · exact .inr (ih.1 hdf)
    · rintro (heq | hin)
      · subst a
        exact Int.dvd_mul_right _ _
      · exact Int.dvd_trans (ih.2 hin) (Int.dvd_mul_left _ _)

theorem factorization_progress_complete__final_result
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hr : 1 ≤ remaining) (hfinished : remaining = 1 ∨ remaining < candidate)
    (hp : FactorizationProgress original factors remaining candidate) :
    PrimeFactorization original factors := by
  obtain ⟨hprod, hprimes, hs, hb, hexc⟩ := hp
  have hr1 : remaining = 1 := by
    rcases hfinished with h1 | hlt
    · exact h1
    · apply Classical.byContradiction
      intro hne
      exact hexc remaining (by omega) ⟨1, by simp⟩
  subst remaining
  simp only [Int.mul_one] at hprod
  refine ⟨hprimes, hs, hprod, ?_⟩
  intro q
  constructor
  · intro hq
    have hprime := hprimes.mem hq
    refine ⟨hprime, ?_⟩
    rw [← hprod]
    exact (prime_divides_factor_product_iff_in__final_result q factors hprime hprimes).2 hq
  · rintro ⟨hprime, hdiv⟩
    rw [← hprod] at hdiv
    exact (prime_divides_factor_product_iff_in__final_result q factors hprime hprimes).1 hdiv

end ProofSupport

open ProofSupport
open Algorithms.integer_divide.lean.groundtruth.integer_divide_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.integer_divide.lean.groundtruth.integer_divide_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_divide_entail_wit_1 : divide_entail_wit_1 := by
  unfold divide_entail_wit_1
  right
  intro p n original heq ho hb
  Exists ([] : List Int)
  split_pure_spatial
  · sep_apply (naive_C_Rules.IntArray.undef_full_split_to_undef_seg p 1 original (by omega))
    simp only [Int.add_zero]
    sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (naive_C_Rules.IntArray.seg_empty p 1 1)).2)
    split_pure_spatial
    · cancel
    · dump_pre_spatial
      rfl
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (exact ⟨by simpa using heq, .nil, .Sorted_nil, .nil,
          fun d hd => by omega⟩)
      | (solve | simp [Zlength])
      | omega
      | int_auto

theorem proof_of_divide_entail_wit_3_1 : divide_entail_wit_3_1 := by
  unfold divide_entail_wit_3_1
  intro p original factors cnt i n hm ho hb hn hno hi hio h1 hc hco hl hp
  have hrem : Z.rem n i = 1 := by
    subst n
    exact Int.tmod_eq_of_lt (by decide) (by omega)
  omega

theorem proof_of_divide_entail_wit_3_2 : divide_entail_wit_3_2 := by
  unfold divide_entail_wit_3_2
  intro p original factors cnt i n hm ho hb hn hno hi hio hin hc hco hl hp
  have hroom := factorization_progress_room__progress_transitions original factors n i hi hin hp
  Right
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | (simp only [INT_MIN]; omega) | int_auto

theorem proof_of_divide_entail_wit_4_1 : divide_entail_wit_4_1 := by
  unfold divide_entail_wit_4_1
  intro p original factors cnt i n hroom hib hnb hii hni hm ho hb hn hno hi hio h1 hc hco hl hp
  have hrem : Z.rem n i = 1 := by
    subst n
    exact Int.tmod_eq_of_lt (by decide) (by omega)
  omega

theorem proof_of_divide_entail_wit_4_2 : divide_entail_wit_4_2 := by
  unfold divide_entail_wit_4_2
  intro p original factors cnt i n hroom hib hnb hii hni hm ho hb hn hno hi hio hin hc hco hl hp
  obtain ⟨hprogress, hcases⟩ :=
    factorization_progress_extract__progress_transitions original factors n i hn hi hin hm hp
  have hqpos : 1 ≤ Z.quot n i := Z.quot_le_lower_bound n i 1 (by omega) (by omega)
  have hqupper : Z.quot n i ≤ original :=
    Z.quot_le_upper_bound n i original (by omega) (by
      have hm := Int.mul_le_mul_of_nonneg_right (show 1 ≤ i by omega) (show 0 ≤ original by omega)
      omega)
  have hlen : Zlength (factors ++ [i]) = cnt + 1 := by
    simp only [Zlength_app, Zlength_cons, Zlength_nil, hl]
    omega
  rcases hcases with h1 | hlarge
  · Left
    Exists (factors ++ [i])
    simp only [Int.add_assoc]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial <;> first | assumption | omega | (simp only [INT_MIN]; omega) | int_auto
  · Right
    Exists (factors ++ [i])
    simp only [Int.add_assoc]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial <;> first | assumption | omega | (simp only [INT_MIN]; omega) | int_auto

theorem proof_of_divide_entail_wit_5_split_goal_1 : divide_entail_wit_5_split_goal_1 := by
  unfold divide_entail_wit_5_split_goal_1
  intro original factors cnt i n hcb hib hnb hci hii hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  have hne : i ≠ n := by
    intro heq
    subst n
    exact hm Int.tmod_self
  omega

theorem proof_of_divide_entail_wit_5 : divide_entail_wit_5 := by
  unfold divide_entail_wit_5
  right
  intro original factors cnt i n hcb hib hnb hci hii hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_divide_entail_wit_5_split_goal_1 original factors cnt i n
      hcb hib hnb hci hii hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp

theorem proof_of_divide_entail_wit_6_split_goal_1 : divide_entail_wit_6_split_goal_1 := by
  unfold divide_entail_wit_6_split_goal_1
  intro original factors cnt i n hib hcb hnb hci hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  exact factorization_progress_advance__progress_transitions original factors n i hi hm hp

theorem proof_of_divide_entail_wit_6 : divide_entail_wit_6 := by
  unfold divide_entail_wit_6
  right
  intro original factors cnt i n hib hcb hnb hci hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_divide_entail_wit_6_split_goal_1 original factors cnt i n
      hib hcb hnb hci hni hn1 hm ho hb hn hno hi hio hin hc hco hl hp

theorem proof_of_divide_return_wit_1 : divide_return_wit_1 := by
  unfold divide_return_wit_1
  right
  intro p original factors cnt i n hin ho hb hn hno hi hib hio hc hco hl hp
  Exists factors
  rw [hl]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact factorization_progress_complete__final_result original factors n i hn (.inr hin) hp
      | omega

theorem proof_of_divide_return_wit_2 : divide_return_wit_2 := by
  unfold divide_return_wit_2
  right
  intro p original factors cnt i n h1 hm ho hb hn hno hi hio h11 hc hco hl hp
  Exists factors
  rw [hl]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact factorization_progress_complete__final_result original factors n i hn (.inl h1) hp
      | omega

end Algorithms.integer_divide.lean.groundtruth.integer_divide_proof_manual
