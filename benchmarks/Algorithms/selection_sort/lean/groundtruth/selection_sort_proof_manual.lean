import Algorithms.selection_sort.lean.groundtruth.selection_sort_goal
import Algorithms.selection_sort.lean.groundtruth.selection_sort_proof_auto
import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import Init.Data.List.Nat.Pairwise
import AUXLib.Arithmetic

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.selection_sort.lean.groundtruth.selection_sort_proof_manual

open Algorithms.selection_sort.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib
export AUXLib.Sorting (increasing_aux increasing lowerbound strict_lowerbound)

private theorem increasing_aux_iff (l : List Int) (x : Int) :
    increasing_aux l x ↔ lowerbound x l ∧ increasing l := by
  induction l generalizing x with
  | nil => simp [Sorting.increasing_aux, Sorting.lowerbound, Sorting.increasing]
  | cons y l ih =>
    constructor
    · intro h
      have hh := (ih y).mp h.2
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      apply Sorting.lowerbound_iff x l |>.2
      intro z hz
      exact Int.le_trans h.1 ((Sorting.lowerbound_iff y l).mp hh.1 z hz)
    · intro h
      exact ⟨h.1.1, h.2⟩

private theorem increasing_pairwise (l : List Int) :
    increasing l ↔ l.Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [Sorting.increasing]
  | cons x l ih =>
    change increasing_aux l x ↔ (x::l).Pairwise (· ≤ ·)
    rw [increasing_aux_iff, List.pairwise_cons, Sorting.lowerbound_iff, ih]

private theorem increasing_Znth (l : List Int) (h : increasing l) (i j : Int)
    (hr : 0 ≤ i ∧ i ≤ j ∧ j < Zlength l) : Znth i l 0 ≤ Znth j l 0 := by
  have hi : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hr; omega
  have hj : j.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hr; omega
  by_cases hij : i = j
  · subst j; exact Int.le_refl _
  have hlt : i.toNat < j.toNat := by omega
  have hp := (List.pairwise_iff_getElem.mp ((increasing_pairwise l).mp h)) i.toNat j.toNat hi hj hlt
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] using hp

private theorem increasing_of_Znth (l : List Int)
    (h : ∀ i j : Int, (0 ≤ i ∧ i ≤ j ∧ j < Zlength l) → Znth i l 0 ≤ Znth j l 0) :
    increasing l := by
  apply (increasing_pairwise l).mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hz := h i j (by simp only [Zlength, Int.ofNat_eq_coe]; omega)
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] using hz

private theorem sublist_length (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi-lo := by
  simp only [Zlength, sublist, List.length_drop, List.length_take, Int.ofNat_eq_coe] at *
  omega

theorem increasing_sublist_elim (l : List Int) (lo hi i j : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : increasing (sublist lo hi l)) (hr : lo ≤ i ∧ i ≤ j ∧ j < hi) :
    Znth i l 0 ≤ Znth j l 0 := by
  have hz := increasing_Znth (sublist lo hi l) h (i-lo) (j-lo)
    (by rw [sublist_length l lo hi hlo hhi]; omega)
  rw [Znth_sublist 0 lo (i-lo) hi l hlo.1 (by omega),
      Znth_sublist 0 lo (j-lo) hi l hlo.1 (by omega)] at hz
  simpa using hz

theorem increasing_sublist_intro (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : ∀ i j, (lo ≤ i ∧ i ≤ j ∧ j < hi) → Znth i l 0 ≤ Znth j l 0) :
    increasing (sublist lo hi l) := by
  apply increasing_of_Znth
  intro i j hr
  rw [sublist_length l lo hi hlo hhi] at hr
  rw [Znth_sublist 0 lo i hi l hlo.1 (by omega), Znth_sublist 0 lo j hi l hlo.1 (by omega)]
  exact h _ _ (by omega)

private theorem perm_replace_head (l : List Int) (k : Nat) (x d : Int) (hk : k < l.length) :
    Permutation (x :: l) (l.getD k d :: replace_nth k l x) := by
  induction l generalizing k x with
  | nil => simp at hk
  | cons y l ih =>
    cases k with
    | zero => exact List.Perm.swap y x l
    | succ k =>
      simp only [List.getD_cons_succ, replace_nth]
      exact (List.Perm.swap y x l).trans
        ((ih k x (by simpa using hk)).cons y |>.trans (List.Perm.swap _ _ _))

private theorem permutation_swap_nat (l : List Int) (i j : Nat) (d : Int)
    (hij : i < j) (hj : j < l.length) :
    Permutation l (replace_nth j (replace_nth i l (l.getD j d)) (l.getD i d)) := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_zero, List.getD_cons_succ] using
          perm_replace_head l j x d (by simpa using hj)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_succ] using
          (ih i j (by omega) (by simpa using hj)).cons x

theorem permutation_swap_Znth_lt (l : List Int) (i j d : Int)
    (hr : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  apply permutation_swap_nat
  · omega
  · simp only [Zlength, Int.ofNat_eq_coe] at hr; omega

end ProofSupport

open ProofSupport
open Algorithms.selection_sort.lean.groundtruth.selection_sort_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.selection_sort.lean.groundtruth.selection_sort_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open ProofSupport

theorem proof_of_sortArray_entail_wit_1_split_goal_1 : sortArray_entail_wit_1_split_goal_1 := by
  unfold sortArray_entail_wit_1_split_goal_1
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1_split_goal_2 : sortArray_entail_wit_1_split_goal_2 := by
  unfold sortArray_entail_wit_1_split_goal_2
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1_split_goal_3 : sortArray_entail_wit_1_split_goal_3 := by
  unfold sortArray_entail_wit_1_split_goal_3
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1 := by
  unfold sortArray_entail_wit_1
  right
  intro numsSize_pre l PreH1 PreH2 PreH3
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_1_split_goal_1 numsSize_pre l) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_1_split_goal_3 numsSize_pre l) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_2_split_goal_1 : sortArray_entail_wit_2_split_goal_1 := by
  unfold sortArray_entail_wit_2_split_goal_1
  intro numsSize_pre l a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    intro q h
    have heq : q = i_2 := by omega
    subst q
    omega

theorem proof_of_sortArray_entail_wit_2_split_goal_2 : sortArray_entail_wit_2_split_goal_2 := by
  unfold sortArray_entail_wit_2_split_goal_2
  intro numsSize_pre l a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2 := by
  unfold sortArray_entail_wit_2
  right
  intro numsSize_pre l a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_2_split_goal_1 numsSize_pre l a_2 i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_2_split_goal_2 numsSize_pre l a_2 i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_3_1_split_goal_1 : sortArray_entail_wit_3_1_split_goal_1 := by
  unfold sortArray_entail_wit_3_1_split_goal_1
  intro numsSize_pre l a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    have hlen : Zlength a_2 = numsSize_pre := by simpa only [Zlength_replace_Znth] using PreH1
    apply increasing_sublist_intro <;> try omega
    intro p q hr
    rw [Znth_replace_Znth_Diff, Znth_replace_Znth_Diff, Znth_replace_Znth_Diff, Znth_replace_Znth_Diff]
    · exact increasing_sublist_elim a_2 0 i_2 p q (by omega) (by omega) PreH11 (by omega)
    all_goals try simp only [Zlength_replace_Znth]
    all_goals omega

theorem proof_of_sortArray_entail_wit_3_1_split_goal_2 : sortArray_entail_wit_3_1_split_goal_2 := by
  unfold sortArray_entail_wit_3_1_split_goal_2
  intro numsSize_pre l a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    have hlen : Zlength a_2 = numsSize_pre := by simpa only [Zlength_replace_Znth] using PreH1
    exact PreH10.trans (permutation_swap_Znth_lt a_2 i_2 j_2 0 (by omega))

theorem proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1 := by
  unfold sortArray_entail_wit_3_1
  right
  intro numsSize_pre l a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_3_1_split_goal_1 numsSize_pre l a_2 j_2 i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_3_1_split_goal_2 numsSize_pre l a_2 j_2 i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_4_split_goal_1 : sortArray_entail_wit_4_split_goal_1 := by
  unfold sortArray_entail_wit_4_split_goal_1
  intro numsSize_pre l a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    intro p q h
    by_cases hp : p < i_2
    · exact PreH11 p q (by omega)
    · have heq : p = i_2 := by omega
      subst p
      exact PreH12 q (by omega)

theorem proof_of_sortArray_entail_wit_4_split_goal_2 : sortArray_entail_wit_4_split_goal_2 := by
  unfold sortArray_entail_wit_4_split_goal_2
  intro numsSize_pre l a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    apply increasing_sublist_intro <;> try omega
    intro p q hr
    by_cases hq : q = i_2
    · subst q
      by_cases hp : p = i_2
      · subst p; omega
      · exact PreH11 p i_2 (by omega)
    · exact increasing_sublist_elim a_2 0 i_2 p q (by omega) (by omega) PreH10 (by omega)

theorem proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4 := by
  unfold sortArray_entail_wit_4
  right
  intro numsSize_pre l a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_4_split_goal_1 numsSize_pre l a_2 j i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_4_split_goal_2 numsSize_pre l a_2 j i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_return_wit_1_split_goal_1 : sortArray_return_wit_1_split_goal_1 := by
  unfold sortArray_return_wit_1_split_goal_1
  intro numsSize_pre l a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    have hi : i = numsSize_pre := by omega
    subst i
    rw [← PreH1] at PreH8
    simpa [sublist, Zlength] using PreH8

theorem proof_of_sortArray_return_wit_1 : sortArray_return_wit_1 := by
  unfold sortArray_return_wit_1
  right
  intro numsSize_pre l a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_return_wit_1_split_goal_1 numsSize_pre l a i) <;> assumption)
      | omega
      | int_auto

end Algorithms.selection_sort.lean.groundtruth.selection_sort_proof_manual
