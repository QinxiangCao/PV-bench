import Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_goal
import Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_proof_auto
import Data_structures.binary_indexed_tree.lean.groundtruth.proof_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_proof_manual

open Data_structures.binary_indexed_tree.lean
open Data_structures.binary_indexed_tree.lean.groundtruth.proof_lib
open Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_goal
open scoped SimpleC

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_goal Data_structures.binary_indexed_tree.lean.groundtruth.proof_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_lowbit_return_wit_1_split_goal_1 : lowbit_return_wit_1_split_goal_1 := by
  unfold lowbit_return_wit_1_split_goal_1
  intro x_pre PreH1 PreH2
  exact FenwickLowbit_le x_pre (by omega)


theorem proof_of_lowbit_return_wit_1_split_goal_2 : lowbit_return_wit_1_split_goal_2 := by
  unfold lowbit_return_wit_1_split_goal_2
  intro x_pre PreH1 PreH2
  exact (FenwickLowbit_bounds x_pre (by omega)).1


theorem proof_of_lowbit_return_wit_1_split_goal_3 : lowbit_return_wit_1_split_goal_3 := by
  unfold lowbit_return_wit_1_split_goal_3
  intro x_pre PreH1 PreH2
  rfl


theorem proof_of_lowbit_return_wit_1 : lowbit_return_wit_1 := by
  unfold lowbit_return_wit_1
  right
  intro x_pre PreH1 PreH2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_lowbit_return_wit_1_split_goal_1 x_pre PreH1 PreH2
      | exact proof_of_lowbit_return_wit_1_split_goal_2 x_pre PreH1 PreH2
      | exact proof_of_lowbit_return_wit_1_split_goal_3 x_pre PreH1 PreH2


theorem proof_of_add_safety_wit_1_split_goal_1 : add_safety_wit_1_split_goal_1 := by
  unfold add_safety_wit_1_split_goal_1
  intro delta_pre pos_pre n_pre bit_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hcov := PreH11.2.2.1 PreH1
  have hcur := (PreH11.2.2.2 pos ⟨PreH6, PreH1⟩).2 (Or.inr (Int.le_refl pos))
  have hnode := PreH8.2.2.2 pos ⟨PreH6, PreH1⟩
  have hpoint := (FenwickNodeSum_add_point__add_node_update a pos_pre delta_pre pos
    (by have := PreH8.1; omega) (by have := PreH8.1; omega)).1 hcov
  have hlo := FenwickNodeLo_bounds pos (by omega)
  have hsafe := PreH10 (FenwickNodeLo pos) pos hlo PreH1
  unfold FenwickNodeSum at hnode hpoint
  dump_pre_spatial
  simp only [INT_MAX]
  omega


theorem proof_of_add_safety_wit_1_split_goal_2 : add_safety_wit_1_split_goal_2 := by
  unfold add_safety_wit_1_split_goal_2
  intro delta_pre pos_pre n_pre bit_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hcov := PreH11.2.2.1 PreH1
  have hcur := (PreH11.2.2.2 pos ⟨PreH6, PreH1⟩).2 (Or.inr (Int.le_refl pos))
  have hnode := PreH8.2.2.2 pos ⟨PreH6, PreH1⟩
  have hpoint := (FenwickNodeSum_add_point__add_node_update a pos_pre delta_pre pos
    (by have := PreH8.1; omega) (by have := PreH8.1; omega)).1 hcov
  have hlo := FenwickNodeLo_bounds pos (by omega)
  have hsafe := PreH10 (FenwickNodeLo pos) pos hlo PreH1
  unfold FenwickNodeSum at hnode hpoint
  dump_pre_spatial
  simp only [INT_MIN]
  omega


theorem proof_of_add_safety_wit_1 : add_safety_wit_1 := by
  unfold add_safety_wit_1
  right
  intro delta_pre pos_pre n_pre bit_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact proof_of_add_safety_wit_1_split_goal_1 delta_pre pos_pre n_pre bit_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_add_safety_wit_1_split_goal_2 delta_pre pos_pre n_pre bit_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_add_entail_wit_1_split_goal_1 : add_entail_wit_1_split_goal_1 := by
  unfold add_entail_wit_1_split_goal_1
  intro delta_pre pos_pre n_pre bit_l a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h; exact FenwickCovers_self pos_pre (by omega)
  · intro node hn
    constructor
    · intro h
      have hc : FenwickNodeLo node ≤ pos_pre ∧ pos_pre ≤ node := h.1
      omega
    · intro h; rfl


theorem proof_of_add_entail_wit_1 : add_entail_wit_1 := by
  unfold add_entail_wit_1
  right
  intro delta_pre pos_pre n_pre bit_l a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_add_entail_wit_1_split_goal_1 delta_pre pos_pre n_pre bit_l a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7


theorem proof_of_add_entail_wit_2_split_goal_1 : add_entail_wit_2_split_goal_1 := by
  unfold add_entail_wit_2_split_goal_1
  intro delta_pre pos_pre n_pre bit_l a bit_cur_2 pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  rw [PreH1]
  obtain ⟨halen, hbitlen, ha0, hnodes⟩ := PreH11
  obtain ⟨hcurlen, hcurzero, hlive, hprogress⟩ := PreH14
  have hposrange : 0 ≤ pos ∧ pos < Zlength bit_cur_2 := by omega
  have hpcov : FenwickCovers pos pos_pre := hlive PreH4
  have hpositive := FenwickLowbit_positive pos (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Zlength_replace_Znth] using hcurlen
  · rw [Znth_replace_Znth_Diff 0 bit_cur_2 pos 0 _ hposrange (by omega) (by omega)]
    exact hcurzero
  · intro hnext
    exact Fenwick_add_successor_covers__add_progress_bitwise pos pos_pre (by omega) hpcov
  · intro node hn
    have hnr : 0 ≤ node ∧ node < Zlength bit_cur_2 := by omega
    obtain ⟨hupdated, hunchanged⟩ := hprogress node hn
    constructor
    · intro hc
      by_cases hlt : node < pos
      · rw [Znth_replace_Znth_Diff 0 bit_cur_2 pos node _ hposrange hnr (by omega)]
        exact hupdated ⟨hc.1, hlt⟩
      · by_cases he : node = pos
        · subst node
          rw [Znth_replace_Znth_Same 0 bit_cur_2 pos _ hposrange,
            hunchanged (Or.inr (Int.le_refl pos))]
        · have hgap := Fenwick_add_successor_gap__add_progress_bitwise pos node (by omega) (by omega)
          have hc1 : FenwickNodeLo node ≤ pos_pre ∧ pos_pre ≤ node := hc.1
          have hc2 : FenwickNodeLo pos ≤ pos_pre ∧ pos_pre ≤ pos := hpcov
          omega
    · intro hc
      by_cases he : node = pos
      · subst node
        obtain hnc | hnext := hc
        · exact False.elim (hnc hpcov)
        · omega
      · rw [Znth_replace_Znth_Diff 0 bit_cur_2 pos node _ hposrange hnr (by omega)]
        apply hunchanged
        obtain hnc | hnext := hc
        · exact Or.inl hnc
        · exact Or.inr (by omega)


theorem proof_of_add_entail_wit_2 : add_entail_wit_2 := by
  unfold add_entail_wit_2
  right
  intro delta_pre pos_pre n_pre bit_l a bit_cur_2 pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_add_entail_wit_2_split_goal_1 delta_pre pos_pre n_pre bit_l a bit_cur_2 pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14


theorem proof_of_add_return_wit_1_split_goal_1 : add_return_wit_1_split_goal_1 := by
  unfold add_return_wit_1_split_goal_1
  intro delta_pre pos_pre n_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH11.2.1


theorem proof_of_add_return_wit_1_split_goal_2 : add_return_wit_1_split_goal_2 := by
  unfold add_return_wit_1_split_goal_2
  intro delta_pre pos_pre n_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  obtain ⟨halen, hbitlen, ha0, hnodes⟩ := PreH8
  obtain ⟨hcurlen, hcurzero, hlive, hprogress⟩ := PreH11
  refine ⟨?_, by omega, ?_, ?_⟩
  · simpa only [FenwickAddArray, Zlength_replace_Znth] using halen
  · unfold FenwickAddArray
    rw [Znth_replace_Znth_Diff 0 a pos_pre 0 _ (by omega) (by omega) (by omega)]
    exact ha0
  · intro node hn
    obtain ⟨hupdated, hunchanged⟩ := hprogress node hn
    have hnode := hnodes node hn
    have hp := FenwickNodeSum_add_point__add_node_update a pos_pre delta_pre node (by omega) (by omega)
    by_cases hc : FenwickCovers node pos_pre
    · rw [hupdated ⟨hc, by omega⟩, hnode]
      exact (hp.1 hc).symm
    · rw [hunchanged (Or.inl hc), hnode]
      exact (hp.2 hc).symm


theorem proof_of_add_return_wit_1 : add_return_wit_1 := by
  unfold add_return_wit_1
  right
  intro delta_pre pos_pre n_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_add_return_wit_1_split_goal_1 delta_pre pos_pre n_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_add_return_wit_1_split_goal_2 delta_pre pos_pre n_pre bit_l a bit_cur pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_query_safety_wit_3_split_goal_1 : query_safety_wit_3_split_goal_1 := by
  unfold query_safety_wit_3_split_goal_1
  intro pos_pre bit_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hs := Fenwick_query_step_int_safe__query_step a bit_l n pos_pre pos sum
    PreH9 PreH10 PreH1 PreH5 PreH6 PreH11
  dump_pre_spatial
  simp only [INT_MAX]
  omega


theorem proof_of_query_safety_wit_3_split_goal_2 : query_safety_wit_3_split_goal_2 := by
  unfold query_safety_wit_3_split_goal_2
  intro pos_pre bit_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hs := Fenwick_query_step_int_safe__query_step a bit_l n pos_pre pos sum
    PreH9 PreH10 PreH1 PreH5 PreH6 PreH11
  dump_pre_spatial
  simp only [INT_MIN]
  omega


theorem proof_of_query_safety_wit_3 : query_safety_wit_3 := by
  unfold query_safety_wit_3
  right
  intro pos_pre bit_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact proof_of_query_safety_wit_3_split_goal_1 pos_pre bit_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_query_safety_wit_3_split_goal_2 pos_pre bit_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_query_entail_wit_1_split_goal_1 : query_entail_wit_1_split_goal_1 := by
  unfold query_entail_wit_1_split_goal_1
  intro pos_pre n bit_l a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact FenwickQueryState_initial a pos_pre


theorem proof_of_query_entail_wit_1 : query_entail_wit_1 := by
  unfold query_entail_wit_1
  right
  intro pos_pre n bit_l a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_query_entail_wit_1_split_goal_1 pos_pre n bit_l a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6


theorem proof_of_query_entail_wit_2_split_goal_1 : query_entail_wit_2_split_goal_1 := by
  unfold query_entail_wit_2_split_goal_1
  intro pos_pre n bit_l a sum pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  rw [PreH1]
  exact FenwickQueryState_step a bit_l n pos_pre pos sum PreH12 (by omega) PreH14


theorem proof_of_query_entail_wit_2_split_goal_2 : query_entail_wit_2_split_goal_2 := by
  unfold query_entail_wit_2_split_goal_2
  intro pos_pre n bit_l a sum pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hs := Fenwick_query_step_int_safe__query_step a bit_l n pos_pre pos sum
    PreH12 PreH13 PreH4 PreH8 PreH9 PreH14
  simp only [INT_MAX]
  omega


theorem proof_of_query_entail_wit_2_split_goal_3 : query_entail_wit_2_split_goal_3 := by
  unfold query_entail_wit_2_split_goal_3
  intro pos_pre n bit_l a sum pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hs := Fenwick_query_step_int_safe__query_step a bit_l n pos_pre pos sum
    PreH12 PreH13 PreH4 PreH8 PreH9 PreH14
  simp only [INT_MIN]
  omega


theorem proof_of_query_entail_wit_2 : query_entail_wit_2 := by
  unfold query_entail_wit_2
  right
  intro pos_pre n bit_l a sum pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_query_entail_wit_2_split_goal_1 pos_pre n bit_l a sum pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_query_entail_wit_2_split_goal_2 pos_pre n bit_l a sum pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_query_entail_wit_2_split_goal_3 pos_pre n bit_l a sum pos retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14


theorem proof_of_query_return_wit_1_split_goal_1 : query_return_wit_1_split_goal_1 := by
  unfold query_return_wit_1_split_goal_1
  intro pos_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : pos = 0 := by omega
  unfold FenwickQueryState at PreH11
  rw [he, FenwickPrefixSum_zero] at PreH11
  omega


theorem proof_of_query_return_wit_1 : query_return_wit_1 := by
  unfold query_return_wit_1
  right
  intro pos_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_query_return_wit_1_split_goal_1 pos_pre n bit_l a sum pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

end Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_proof_manual
