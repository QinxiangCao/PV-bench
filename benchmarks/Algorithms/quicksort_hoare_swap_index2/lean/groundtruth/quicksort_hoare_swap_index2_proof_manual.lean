import Algorithms.quicksort_hoare_swap_index2.lean.groundtruth.quicksort_hoare_swap_index2_goal
import Algorithms.quicksort_hoare_swap_index2.lean.groundtruth.quicksort_hoare_swap_index2_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.quicksort_hoare_swap_index2.lean.groundtruth.quicksort_hoare_swap_index2_proof_manual

open Algorithms.quicksort_hoare_swap_index2.lean
open scoped SimpleC

namespace ProofSupport

export SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib (
  same_outside_range
  partitioned_at
  range_nondecreasing
  same_outside_range_trans_local
  Forall_Znth_local
  Forall_sublist_by_Znth_local
  same_outside_range_swap_inside_local
  same_outside_range_replace_inside_local
  list_split_around_two_indices_local
  sublist_suffix_full_local
  replace_Znth_decomp_local
  swap_Znth_perm_local
  partition_outer_exit_swap_yields_partitioned_at
  range_nondecreasing_full_to_increasing
  same_outside_range_weaken_local
  Forall_permutation_local
  sublist_eq_from_Znth_local
  list_decompose_sublist_local
  same_outside_range_prefix_local
  same_outside_range_suffix_local
  middle_permutation_of_same_outside_local
  partitioned_at_preserved_by_left_local
  partitioned_at_preserved_by_right_local
  partitioned_at_left_Znth_le_local
  partitioned_at_right_Znth_ge_local
  range_nondecreasing_ext_local
  quicksort_partition_combine_right_only_local
  quicksort_partition_combine_left_only_local
  quicksort_partition_combine_both_sides_local
  replace_nth_comm_Z_local
  replace_Znth_comm_local
  replace_nth_twice_Z_local
  replace_Znth_twice_local
  partition_hole_outer_fill_left_perm_split_local
  partition_hole_left_fill_right_perm_split_local
  partition_hole_outer_exit_partitioned_split_local
  partition_hole_left_exit_partitioned_split_local
  quicksort_partition_combine_right_guard_local
  quicksort_partition_combine_left_guard_local
  quicksort_partition_combine_short_local
  int_array_full_merge_three_local
  quicksort_permuted_partition_combine_local
  increasing_length_le_1
  lomuto_replace_Znth_swap_form
  lomuto_permutation_swap_Znth_lt
  lomuto_replace_nth_comm_Z
  lomuto_replace_Znth_comm
  lomuto_permutation_swap_Znth
  lomuto_permutation_swap_Znth_by_result_length
  same_outside_range_refl
  same_outside_range_trans
  same_outside_range_weaken
  Forall_permutation
  lomuto_Forall_Znth
  lomuto_Znth_replace_eq
  lomuto_Znth_replace_neq
  sublist_eq_from_Znth
  lomuto_list_decompose_sublist
  same_outside_range_prefix
  same_outside_range_suffix
  middle_permutation_of_same_outside
  lomuto_Forall_sublist_by_Znth
  same_outside_range_swap_inside
  partitioned_at_after_lomuto_final_swap
  increasing increasing_aux)
export AUXLib (Permutation)

end ProofSupport

open ProofSupport
open Algorithms.quicksort_hoare_swap_index2.lean.groundtruth.quicksort_hoare_swap_index2_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.quicksort_hoare_swap_index2.lean.groundtruth.quicksort_hoare_swap_index2_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Preserve residual VCs and the split/cancel SL strategy. Goal_apply is
-- explicitly instantiated; pure predicates use the same split theorem directly.
private theorem manual_read_swap (l : List Int) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l)
    (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 =
    if k = j then Znth i l 0 else if k = i then Znth j l 0 else Znth k l 0 := by
  by_cases he : k = j
  · subst k; rw [if_pos rfl]; exact Znth_replace_Znth_Same 0 _ j _ (by simpa only [Zlength_replace_Znth] using hj)
  · rw [if_neg he, Znth_replace_Znth_Diff 0 _ j k _ (by simpa only [Zlength_replace_Znth] using hj)
      (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm he)]
    by_cases he' : k = i
    · subst k; rw [if_pos rfl]; exact Znth_replace_Znth_Same 0 l i _ hi
    · rw [if_neg he']; exact Znth_replace_Znth_Diff 0 l i k _ hi hk (Ne.symm he')

theorem proof_of_partition_entail_wit_1_split_goal_1 : partition_entail_wit_1_split_goal_1 := by
  unfold partition_entail_wit_1_split_goal_1
  intro high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro k hk
  omega


theorem proof_of_partition_entail_wit_1_split_goal_2 : partition_entail_wit_1_split_goal_2 := by
  unfold partition_entail_wit_1_split_goal_2
  intro high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro k hk
  omega


theorem proof_of_partition_entail_wit_1_split_goal_3 : partition_entail_wit_1_split_goal_3 := by
  unfold partition_entail_wit_1_split_goal_3
  intro high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact same_outside_range_refl l low_pre high_pre


theorem proof_of_partition_entail_wit_1_split_goal_4 : partition_entail_wit_1_split_goal_4 := by
  unfold partition_entail_wit_1_split_goal_4
  intro high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact List.Perm.refl l


theorem proof_of_partition_entail_wit_1 : partition_entail_wit_1 := by
  unfold partition_entail_wit_1
  right
  intro high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_1 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact proof_of_partition_entail_wit_1_split_goal_1 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_2 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact proof_of_partition_entail_wit_1_split_goal_2 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_3 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact proof_of_partition_entail_wit_1_split_goal_3 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_4 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact proof_of_partition_entail_wit_1_split_goal_4 high_pre low_pre n l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6


theorem proof_of_partition_entail_wit_5_split_goal_1 : partition_entail_wit_5_split_goal_1 := by
  unfold partition_entail_wit_5_split_goal_1
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  intro he
  rw [he]
  have := PreH18 PreH3
  omega


theorem proof_of_partition_entail_wit_5 : partition_entail_wit_5 := by
  unfold partition_entail_wit_5
  right
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_entail_wit_5_split_goal_1 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact proof_of_partition_entail_wit_5_split_goal_1 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19


theorem proof_of_partition_entail_wit_6_1_split_goal_1 : partition_entail_wit_6_1_split_goal_1 := by
  unfold partition_entail_wit_6_1_split_goal_1
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [Zlength_replace_Znth] at PreH1
  intro k hk
  rw [manual_read_swap l1_2 i_2 j_2 k (by omega) (by omega) (by omega), if_neg (by omega), if_neg (by omega)]
  have := PreH18 k hk
  omega


theorem proof_of_partition_entail_wit_6_1_split_goal_2 : partition_entail_wit_6_1_split_goal_2 := by
  unfold partition_entail_wit_6_1_split_goal_2
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [Zlength_replace_Znth] at PreH1
  intro k hk
  rw [manual_read_swap l1_2 i_2 j_2 k (by omega) (by omega) (by omega), if_neg (by omega), if_neg (by omega)]
  have := PreH17 k hk
  omega


theorem proof_of_partition_entail_wit_6_1_split_goal_3 : partition_entail_wit_6_1_split_goal_3 := by
  unfold partition_entail_wit_6_1_split_goal_3
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [Zlength_replace_Znth] at PreH1
  rw [manual_read_swap l1_2 i_2 j_2 i_2 (by omega) (by omega) (by omega), if_neg (by omega), if_pos rfl]
  have := PreH19 PreH2
  omega


theorem proof_of_partition_entail_wit_6_1_split_goal_4 : partition_entail_wit_6_1_split_goal_4 := by
  unfold partition_entail_wit_6_1_split_goal_4
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [Zlength_replace_Znth] at PreH1
  exact same_outside_range_trans_local l l1_2 _ low_pre high_pre PreH16
    (same_outside_range_swap_inside_local l1_2 low_pre high_pre i_2 j_2 PreH8 (by omega) (by omega) (by omega))


theorem proof_of_partition_entail_wit_6_1_split_goal_5 : partition_entail_wit_6_1_split_goal_5 := by
  unfold partition_entail_wit_6_1_split_goal_5
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [Zlength_replace_Znth] at PreH1
  exact PreH15.trans (swap_Znth_perm_local l1_2 i_2 j_2 (by omega))


theorem proof_of_partition_entail_wit_6_1_split_goal_6 : partition_entail_wit_6_1_split_goal_6 := by
  unfold partition_entail_wit_6_1_split_goal_6
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simp only [Zlength_replace_Znth] at PreH1
  have hne : low_pre ≠ i_2 := by
    intro he
    rw [← he] at PreH3
    omega
  rw [manual_read_swap l1_2 i_2 j_2 low_pre (by omega) (by omega) (by omega), if_neg (by omega), if_neg hne]
  exact PreH14


theorem proof_of_partition_entail_wit_6_1 : partition_entail_wit_6_1 := by
  unfold partition_entail_wit_6_1
  right
  intro high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_entail_wit_6_1_split_goal_1 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact proof_of_partition_entail_wit_6_1_split_goal_1 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (solve | Goal_apply (proof_of_partition_entail_wit_6_1_split_goal_2 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact proof_of_partition_entail_wit_6_1_split_goal_2 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (solve | Goal_apply (proof_of_partition_entail_wit_6_1_split_goal_3 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact proof_of_partition_entail_wit_6_1_split_goal_3 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (solve | Goal_apply (proof_of_partition_entail_wit_6_1_split_goal_4 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact proof_of_partition_entail_wit_6_1_split_goal_4 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (solve | Goal_apply (proof_of_partition_entail_wit_6_1_split_goal_5 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact proof_of_partition_entail_wit_6_1_split_goal_5 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | (solve | Goal_apply (proof_of_partition_entail_wit_6_1_split_goal_6 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact proof_of_partition_entail_wit_6_1_split_goal_6 high_pre low_pre n l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20


theorem proof_of_partition_return_wit_1_split_goal_1 : partition_return_wit_1_split_goal_1 := by
  unfold partition_return_wit_1_split_goal_1
  intro high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [Zlength_replace_Znth] at PreH1
  rw [← PreH12]
  exact partition_outer_exit_swap_yields_partitioned_at l l1_2 low_pre high_pre pivot i j PreH6
    (by have := PreH14.1; omega) ⟨PreH9, PreH10⟩ PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH2


theorem proof_of_partition_return_wit_1_split_goal_2 : partition_return_wit_1_split_goal_2 := by
  unfold partition_return_wit_1_split_goal_2
  intro high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [Zlength_replace_Znth] at PreH1
  rw [← PreH12]
  exact same_outside_range_trans_local l l1_2 _ low_pre high_pre PreH14
    (same_outside_range_swap_inside_local l1_2 low_pre high_pre low_pre i PreH6 (by omega) (by omega) (by omega))


theorem proof_of_partition_return_wit_1_split_goal_3 : partition_return_wit_1_split_goal_3 := by
  unfold partition_return_wit_1_split_goal_3
  intro high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [Zlength_replace_Znth] at PreH1
  rw [← PreH12]
  exact PreH13.trans (lomuto_permutation_swap_Znth l1_2 low_pre i 0 (by omega) (by omega))


theorem proof_of_partition_return_wit_1 : partition_return_wit_1 := by
  unfold partition_return_wit_1
  right
  intro high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_1 high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
      | exact proof_of_partition_return_wit_1_split_goal_1 high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_2 high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
      | exact proof_of_partition_return_wit_1_split_goal_2 high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_3 high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
      | exact proof_of_partition_return_wit_1_split_goal_3 high_pre low_pre n l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17


theorem proof_of_quicksort_range_return_wit_1_split_goal_1 : quicksort_range_return_wit_1_split_goal_1 := by
  unfold quicksort_range_return_wit_1_split_goal_1
  intro right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hl3 := PreH3.1
  have hl2 := PreH7.1
  have hp3 := partitioned_at_preserved_by_left_local l1_2 l1_3 left_pre right_pre retval PreH6 PreH17 PreH7 (by omega) PreH14
  have hp4 := partitioned_at_preserved_by_right_local l1_3 l1_4 left_pre right_pre retval PreH2 PreH17 PreH3 (by omega) hp3
  have hsl : range_nondecreasing l1_4 left_pre (retval - 1) := by
    apply range_nondecreasing_ext_local l1_3 l1_4 left_pre (retval - 1) hl3 _ PreH8
    intro k hk
    exact PreH3.2 k (by omega) (Or.inl (by omega))
  exact quicksort_partition_combine_both_sides_local l1_4 left_pre right_pre retval PreH17 (by omega) ⟨PreH10, PreH11⟩ hp4 hsl PreH4


theorem proof_of_quicksort_range_return_wit_1_split_goal_2 : quicksort_range_return_wit_1_split_goal_2 := by
  unfold quicksort_range_return_wit_1_split_goal_2
  intro right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have h1 := same_outside_range_weaken_local l1_2 l1_3 left_pre (retval - 1) left_pre right_pre (by omega) (by omega) PreH7
  have h2 := same_outside_range_weaken_local l1_3 l1_4 (retval + 1) right_pre left_pre right_pre (by omega) (by omega) PreH3
  exact same_outside_range_trans_local l l1_3 l1_4 left_pre right_pre
    (same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH13 h1) h2


theorem proof_of_quicksort_range_return_wit_1_split_goal_3 : quicksort_range_return_wit_1_split_goal_3 := by
  unfold quicksort_range_return_wit_1_split_goal_3
  intro right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH12.trans (PreH6.trans PreH2)


theorem proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1 := by
  unfold quicksort_range_return_wit_1
  right
  intro right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_1 right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact proof_of_quicksort_range_return_wit_1_split_goal_1 right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_2 right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact proof_of_quicksort_range_return_wit_1_split_goal_2 right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_3 right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact proof_of_quicksort_range_return_wit_1_split_goal_3 right_pre left_pre n l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19


theorem proof_of_quicksort_range_return_wit_2_split_goal_1 : quicksort_range_return_wit_2_split_goal_1 := by
  unfold quicksort_range_return_wit_2_split_goal_1
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hlen := PreH3.1
  have hp := partitioned_at_preserved_by_right_local l1_2 l1_3 left_pre right_pre retval PreH2 PreH14 PreH3 (by omega) PreH11
  exact quicksort_partition_combine_right_guard_local l1_3 left_pre right_pre retval PreH14 (by omega) ⟨PreH7, PreH8⟩ PreH6 hp PreH4


theorem proof_of_quicksort_range_return_wit_2_split_goal_2 : quicksort_range_return_wit_2_split_goal_2 := by
  unfold quicksort_range_return_wit_2_split_goal_2
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH10
    (same_outside_range_weaken_local l1_2 l1_3 (retval + 1) right_pre left_pre right_pre (by omega) (by omega) PreH3)


theorem proof_of_quicksort_range_return_wit_2_split_goal_3 : quicksort_range_return_wit_2_split_goal_3 := by
  unfold quicksort_range_return_wit_2_split_goal_3
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH9.trans PreH2


theorem proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2 := by
  unfold quicksort_range_return_wit_2
  right
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_1 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact proof_of_quicksort_range_return_wit_2_split_goal_1 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_2 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact proof_of_quicksort_range_return_wit_2_split_goal_2 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_3 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact proof_of_quicksort_range_return_wit_2_split_goal_3 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_quicksort_range_return_wit_3_split_goal_1 : quicksort_range_return_wit_3_split_goal_1 := by
  unfold quicksort_range_return_wit_3_split_goal_1
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hlen := PreH4.1
  have hp := partitioned_at_preserved_by_left_local l1_2 l1_3 left_pre right_pre retval PreH3 PreH14 PreH4 (by omega) PreH11
  exact quicksort_partition_combine_left_guard_local l1_3 left_pre right_pre retval PreH14 (by omega) ⟨PreH7, PreH8⟩ PreH2 hp PreH5


theorem proof_of_quicksort_range_return_wit_3_split_goal_2 : quicksort_range_return_wit_3_split_goal_2 := by
  unfold quicksort_range_return_wit_3_split_goal_2
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH10
    (same_outside_range_weaken_local l1_2 l1_3 left_pre (retval - 1) left_pre right_pre (by omega) (by omega) PreH4)


theorem proof_of_quicksort_range_return_wit_3_split_goal_3 : quicksort_range_return_wit_3_split_goal_3 := by
  unfold quicksort_range_return_wit_3_split_goal_3
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH9.trans PreH3


theorem proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3 := by
  unfold quicksort_range_return_wit_3
  right
  intro right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_1 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact proof_of_quicksort_range_return_wit_3_split_goal_1 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_2 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact proof_of_quicksort_range_return_wit_3_split_goal_2 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_3 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact proof_of_quicksort_range_return_wit_3_split_goal_3 right_pre left_pre n l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_quicksort_range_return_wit_4_split_goal_1 : quicksort_range_return_wit_4_split_goal_1 := by
  unfold quicksort_range_return_wit_4_split_goal_1
  intro right_pre left_pre n l l1_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact quicksort_partition_combine_short_local l1_2 left_pre right_pre retval PreH11 (by omega) ⟨PreH4, PreH5⟩ PreH3 PreH2 PreH8


theorem proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4 := by
  unfold quicksort_range_return_wit_4
  right
  intro right_pre left_pre n l l1_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_4_split_goal_1 right_pre left_pre n l l1_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
      | exact proof_of_quicksort_range_return_wit_4_split_goal_1 right_pre left_pre n l l1_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13


theorem proof_of_quicksort_return_wit_1_split_goal_1 : quicksort_return_wit_1_split_goal_1 := by
  unfold quicksort_return_wit_1_split_goal_1
  intro n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  apply range_nondecreasing_full_to_increasing
  simpa only [PreH1] using PreH4


theorem proof_of_quicksort_return_wit_1 : quicksort_return_wit_1 := by
  unfold quicksort_return_wit_1
  right
  intro n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_return_wit_1_split_goal_1 n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7))
      | exact proof_of_quicksort_return_wit_1_split_goal_1 n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7


theorem proof_of_quicksort_return_wit_2_split_goal_1 : quicksort_return_wit_2_split_goal_1 := by
  unfold quicksort_return_wit_2_split_goal_1
  intro n_pre l PreH1 PreH2 PreH3 PreH4
  exact increasing_length_le_1 l (by omega)


theorem proof_of_quicksort_return_wit_2_split_goal_2 : quicksort_return_wit_2_split_goal_2 := by
  unfold quicksort_return_wit_2_split_goal_2
  intro n_pre l PreH1 PreH2 PreH3 PreH4
  exact List.Perm.refl l


theorem proof_of_quicksort_return_wit_2 : quicksort_return_wit_2 := by
  unfold quicksort_return_wit_2
  right
  intro n_pre l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_return_wit_2_split_goal_1 n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact proof_of_quicksort_return_wit_2_split_goal_1 n_pre l PreH1 PreH2 PreH3 PreH4
      | (solve | Goal_apply (proof_of_quicksort_return_wit_2_split_goal_2 n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact proof_of_quicksort_return_wit_2_split_goal_2 n_pre l PreH1 PreH2 PreH3 PreH4

end Algorithms.quicksort_hoare_swap_index2.lean.groundtruth.quicksort_hoare_swap_index2_proof_manual
