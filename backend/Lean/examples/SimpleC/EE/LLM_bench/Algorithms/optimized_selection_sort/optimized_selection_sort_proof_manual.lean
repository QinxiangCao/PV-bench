import SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

open optimized_selection_sort_lib
open SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib

private theorem swapped_lookup (l : List Int) (i m k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hm : 0 ≤ m ∧ m < Zlength l)
    (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth m (Znth i l 0) (replace_Znth i (Znth m l 0) l)) 0 =
      if k = m then Znth i l 0 else if k = i then Znth m l 0 else Znth k l 0 := by
  by_cases hkm : k = m
  · subst k
    rw [if_pos rfl]
    apply Znth_replace_Znth_Same
    simpa only [Zlength_replace_Znth] using hm
  · rw [if_neg hkm, Znth_replace_Znth_Diff 0 _ m k _
      (by simpa only [Zlength_replace_Znth] using hm)
      (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm hkm)]
    by_cases hki : k = i
    · subst k
      rw [if_pos rfl]
      exact Znth_replace_Znth_Same 0 l i _ hi
    · rw [if_neg hki]
      exact Znth_replace_Znth_Diff 0 l i k _ hi hk (Ne.symm hki)

private theorem extend_sorted_prefix (l : List Int) (i : Int)
    (hi : 0 ≤ i) (hlen : i + 1 ≤ Zlength l)
    (hsorted : increasing (sublist 0 i l))
    (hbound : ∀ p, 0 ≤ p ∧ p < i → Znth p l 0 ≤ Znth i l 0) :
    increasing (sublist 0 (i + 1) l) := by
  apply increasing_sublist_intro l 0 (i + 1) (by omega) hlen
  intro p q hpq
  by_cases hq : q < i
  · exact increasing_sublist_elim l 0 i p q (by omega) (by omega) hsorted (by omega)
  · have hqi : q = i := by omega
    subst q
    by_cases hp : p = i
    · subst p; exact Int.le_refl _
    · exact hbound p (by omega)

-- These five Coq declarations were Admitted; their Lean proofs are completed here.
theorem proof_of_optimized_selection_sort_entail_wit_1 : optimized_selection_sort_entail_wit_1 := by
  unfold optimized_selection_sort_entail_wit_1
  right
  intro n input hn hnmax hlen
  have hsorted : increasing (sublist 0 0 input) := by simp [Sorting.increasing, sublist]
  have hperm : Permutation input input := List.Perm.refl _
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first | exact hsorted | exact hperm | (intro p q h; omega)

theorem proof_of_optimized_selection_sort_entail_wit_2 : optimized_selection_sort_entail_wit_2 := by
  unfold optimized_selection_sort_entail_wit_2
  right
  intro n input i l hloop hn hnmax hinput hlen hi hin himax hperm hsorted hcross
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | exact hcross
    | (intro q h
       have hqi : q = i := by omega
       subst q
       exact Int.le_refl _)

theorem proof_of_optimized_selection_sort_entail_wit_4_1 : optimized_selection_sort_entail_wit_4_1 := by
  unfold optimized_selection_sort_entail_wit_4_1
  right
  intro n input j m i l hnewlen hne hj hn hnmax hinput hlen hi hloop him hmj hij hjn
    hperm hsorted hcross hmin
  let swapped := replace_Znth m (Znth i l 0) (replace_Znth i (Znth m l 0) l)
  have hir : 0 ≤ i ∧ i < Zlength l := by omega
  have hmr : 0 ≤ m ∧ m < Zlength l := by omega
  have himlt : i < m := by omega
  have hbefore (k : Int) (hk : 0 ≤ k ∧ k < i) : Znth k swapped 0 = Znth k l 0 := by
    change Znth k (replace_Znth m _ (replace_Znth i _ l)) 0 = _
    rw [swapped_lookup l i m k hir hmr (by omega), if_neg (by omega), if_neg (by omega)]
  have hat_i : Znth i swapped 0 = Znth m l 0 := by
    change Znth i (replace_Znth m _ (replace_Znth i _ l)) 0 = _
    rw [swapped_lookup l i m i hir hmr hir, if_neg (by omega), if_pos rfl]
  have hat_m : Znth m swapped 0 = Znth i l 0 := by
    change Znth m (replace_Znth m _ (replace_Znth i _ l)) 0 = _
    rw [swapped_lookup l i m m hir hmr hmr, if_pos rfl]
  have hafter (k : Int) (hk : i < k ∧ k < n) (hkm : k ≠ m) :
      Znth k swapped 0 = Znth k l 0 := by
    change Znth k (replace_Znth m _ (replace_Znth i _ l)) 0 = _
    rw [swapped_lookup l i m k hir hmr (by omega), if_neg hkm, if_neg (by omega)]
  have hcross_new : ∀ p q : Int,
      (((0 ≤ p ∧ p < i + 1) ∧ i + 1 ≤ q) ∧ q < n) →
      Znth p swapped 0 ≤ Znth q swapped 0 := by
    intro p q hpq
    by_cases hpi : p = i
    · subst p
      rw [hat_i]
      by_cases hqm : q = m
      · subst q; rw [hat_m]; exact hmin i (by omega)
      · rw [hafter q (by omega) hqm]; exact hmin q (by omega)
    · rw [hbefore p (by omega)]
      by_cases hqm : q = m
      · subst q; rw [hat_m]; exact hcross p i (by omega)
      · rw [hafter q (by omega) hqm]; exact hcross p q (by omega)
  have hsorted_new : increasing (sublist 0 (i + 1) swapped) := by
    apply increasing_sublist_intro swapped 0 (i + 1) (by omega)
      (by rw [show Zlength swapped = n from hnewlen]; omega)
    intro p q hpq
    by_cases hqi : q < i
    · rw [hbefore p (by omega), hbefore q (by omega)]
      exact increasing_sublist_elim l 0 i p q (by omega) (by omega) hsorted (by omega)
    · have hq : q = i := by omega
      subst q
      by_cases hp : p = i
      · subst p; exact Int.le_refl _
      · rw [hbefore p (by omega), hat_i]
        exact hcross p m (by omega)
  have hperm_new : Permutation input swapped :=
    hperm.trans (permutation_swap_Znth_lt l i m 0 (by omega))
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first | exact hcross_new | exact hsorted_new | exact hperm_new

theorem proof_of_optimized_selection_sort_entail_wit_4_2 : optimized_selection_sort_entail_wit_4_2 := by
  unfold optimized_selection_sort_entail_wit_4_2
  right
  intro n input j m i l hmi hj hn hnmax hinput hlen hi hloop him hmj hij hjn
    hperm hsorted hcross hmin
  subst m
  have hcross_new : ∀ p q : Int,
      (((0 ≤ p ∧ p < i + 1) ∧ i + 1 ≤ q) ∧ q < n) → Znth p l 0 ≤ Znth q l 0 := by
    intro p q hpq
    by_cases hp : p < i
    · exact hcross p q (by omega)
    · have hpi : p = i := by omega
      subst p
      exact hmin q (by omega)
  have hsorted_new : increasing (sublist 0 (i + 1) l) :=
    extend_sorted_prefix l i hi (by omega) hsorted (fun p hp => hcross p i (by omega))
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first | exact hcross_new | exact hsorted_new

theorem proof_of_optimized_selection_sort_return_wit_1 : optimized_selection_sort_return_wit_1 := by
  unfold optimized_selection_sort_return_wit_1
  right
  intro n input i l hdone hn hnmax hinput hlen hi hin himax hperm hsorted hcross
  have hsorted_all : increasing l := by
    rw [← sublist_self l n hlen.symm]
    apply increasing_sublist_intro l 0 n (by omega) (by omega)
    intro p q hpq
    by_cases hqi : q < i
    · exact increasing_sublist_elim l 0 i p q (by omega) (by omega) hsorted (by omega)
    · by_cases hpi : p < i
      · exact hcross p q (by omega)
      · have hpqeq : p = q := by omega
        subst q; exact Int.le_refl _
  have hresult : optimized_selection_sort_result input l := ⟨hperm, hsorted_all⟩
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first | exact hsorted_all | exact hresult

end SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_proof_manual
