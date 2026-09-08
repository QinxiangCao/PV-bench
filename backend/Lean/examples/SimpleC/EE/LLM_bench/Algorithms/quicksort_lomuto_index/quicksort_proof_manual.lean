import SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_goal
import SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open quicksort_goal quicksort_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Preserve the original residual VCs and execute the split/cancel SL strategy.
-- Goal_apply uses explicit arguments; pure predicate conclusions can require
-- direct application of the same split theorem after spatial preprocessing.

theorem proof_of_partition_entail_wit_1_split_goal_1 : partition_entail_wit_1_split_goal_1 := by
  unfold partition_entail_wit_1_split_goal_1
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  intro k hk
  omega

theorem proof_of_partition_entail_wit_1_split_goal_2 : partition_entail_wit_1_split_goal_2 := by
  unfold partition_entail_wit_1_split_goal_2
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  intro k hk
  omega

theorem proof_of_partition_entail_wit_1_split_goal_3 : partition_entail_wit_1_split_goal_3 := by
  unfold partition_entail_wit_1_split_goal_3
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  exact same_outside_range_refl l low_pre high_pre

theorem proof_of_partition_entail_wit_1_split_goal_4 : partition_entail_wit_1_split_goal_4 := by
  unfold partition_entail_wit_1_split_goal_4
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  exact List.Perm.refl l

theorem proof_of_partition_entail_wit_1 : partition_entail_wit_1 := by
  unfold partition_entail_wit_1
  right
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_1 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_1 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_2 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_2 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_3 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_3 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_4 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_4 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | trivial

theorem proof_of_partition_entail_wit_2_1_split_goal_1 : partition_entail_wit_2_1_split_goal_1 := by
  unfold partition_entail_wit_2_1_split_goal_1
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [Zlength_replace_Znth] at PreH1
  rw [lomuto_Znth_replace_neq (replace_Znth (i_2+1) (Znth j_2 l1_2 0) l1_2) high_pre j_2 (Znth (i_2+1) l1_2 0) 0 (by simp only [Zlength_replace_Znth]; omega) (by omega) (by omega),
    lomuto_Znth_replace_neq l1_2 high_pre (i_2+1) (Znth j_2 l1_2 0) 0 (by omega) (by omega) (by omega)]
  exact PreH13

theorem proof_of_partition_entail_wit_2_1_split_goal_2 : partition_entail_wit_2_1_split_goal_2 := by
  unfold partition_entail_wit_2_1_split_goal_2
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [Zlength_replace_Znth] at PreH1
  exact same_outside_range_trans l l1_2 _ low_pre high_pre PreH12
    (same_outside_range_swap_inside l1_2 low_pre high_pre (i_2+1) j_2 PreH5 (by omega) (by omega) (by omega))

theorem proof_of_partition_entail_wit_2_1_split_goal_3 : partition_entail_wit_2_1_split_goal_3 := by
  unfold partition_entail_wit_2_1_split_goal_3
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [Zlength_replace_Znth] at PreH1
  exact PreH11.trans (lomuto_permutation_swap_Znth l1_2 (i_2+1) j_2 0 (by omega) (by omega))

theorem proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1 := by
  unfold partition_entail_wit_2_1
  right
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_entail_wit_2_1_split_goal_1 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
      | exact (proof_of_partition_entail_wit_2_1_split_goal_1 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
      | (solve | Goal_apply (proof_of_partition_entail_wit_2_1_split_goal_2 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
      | exact (proof_of_partition_entail_wit_2_1_split_goal_2 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
      | (solve | Goal_apply (proof_of_partition_entail_wit_2_1_split_goal_3 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
      | exact (proof_of_partition_entail_wit_2_1_split_goal_3 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
      | trivial

theorem proof_of_partition_return_wit_1_split_goal_1 : partition_return_wit_1_split_goal_1 := by
  unfold partition_return_wit_1_split_goal_1
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  simp only [Zlength_replace_Znth] at PreH1
  have hj : j = high_pre := by omega
  rw [hj] at PreH14
  rw [← PreH12]
  exact partitioned_at_after_lomuto_final_swap l1_2 low_pre high_pre pivot i PreH4 (by omega) PreH7 (by omega) PreH12 PreH13 PreH14

theorem proof_of_partition_return_wit_1_split_goal_2 : partition_return_wit_1_split_goal_2 := by
  unfold partition_return_wit_1_split_goal_2
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  simp only [Zlength_replace_Znth] at PreH1
  rw [← PreH12]
  exact same_outside_range_trans l l1_2 _ low_pre high_pre PreH11
    (same_outside_range_swap_inside l1_2 low_pre high_pre (i+1) high_pre PreH4 (by omega) (by omega) (by omega))

theorem proof_of_partition_return_wit_1_split_goal_3 : partition_return_wit_1_split_goal_3 := by
  unfold partition_return_wit_1_split_goal_3
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  simp only [Zlength_replace_Znth] at PreH1
  rw [← PreH12]
  exact PreH10.trans (lomuto_permutation_swap_Znth l1_2 (i+1) high_pre 0 (by omega) (by omega))

theorem proof_of_partition_return_wit_1 : partition_return_wit_1 := by
  unfold partition_return_wit_1
  right
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_1 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
      | exact (proof_of_partition_return_wit_1_split_goal_1 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_2 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
      | exact (proof_of_partition_return_wit_1_split_goal_2 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_3 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
      | exact (proof_of_partition_return_wit_1_split_goal_3 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | trivial

theorem proof_of_quicksort_range_return_wit_1_split_goal_1 : quicksort_range_return_wit_1_split_goal_1 := by
  unfold quicksort_range_return_wit_1_split_goal_1
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
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
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have h1 := same_outside_range_weaken_local l1_2 l1_3 left_pre (retval - 1) left_pre right_pre (by omega) (by omega) PreH7
  have h2 := same_outside_range_weaken_local l1_3 l1_4 (retval + 1) right_pre left_pre right_pre (by omega) (by omega) PreH3
  exact same_outside_range_trans_local l l1_3 l1_4 left_pre right_pre
    (same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH13 h1) h2

theorem proof_of_quicksort_range_return_wit_1_split_goal_3 : quicksort_range_return_wit_1_split_goal_3 := by
  unfold quicksort_range_return_wit_1_split_goal_3
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH12.trans (PreH6.trans PreH2)

theorem proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1 := by
  unfold quicksort_range_return_wit_1
  right
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact (proof_of_quicksort_range_return_wit_1_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact (proof_of_quicksort_range_return_wit_1_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact (proof_of_quicksort_range_return_wit_1_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | trivial

theorem proof_of_quicksort_range_return_wit_2_split_goal_1 : quicksort_range_return_wit_2_split_goal_1 := by
  unfold quicksort_range_return_wit_2_split_goal_1
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hlen := PreH3.1
  have hp := partitioned_at_preserved_by_right_local l1_2 l1_3 left_pre right_pre retval PreH2 PreH14 PreH3 (by omega) PreH11
  exact quicksort_partition_combine_right_only_local l1_3 left_pre right_pre retval PreH14 (by omega) (by omega) hp PreH4

theorem proof_of_quicksort_range_return_wit_2_split_goal_2 : quicksort_range_return_wit_2_split_goal_2 := by
  unfold quicksort_range_return_wit_2_split_goal_2
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH10
    (same_outside_range_weaken_local l1_2 l1_3 (retval + 1) right_pre left_pre right_pre (by omega) (by omega) PreH3)

theorem proof_of_quicksort_range_return_wit_2_split_goal_3 : quicksort_range_return_wit_2_split_goal_3 := by
  unfold quicksort_range_return_wit_2_split_goal_3
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH9.trans PreH2

theorem proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2 := by
  unfold quicksort_range_return_wit_2
  right
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_2_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_2_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_2_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | trivial

theorem proof_of_quicksort_range_return_wit_3_split_goal_1 : quicksort_range_return_wit_3_split_goal_1 := by
  unfold quicksort_range_return_wit_3_split_goal_1
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hlen := PreH4.1
  have hp := partitioned_at_preserved_by_left_local l1_2 l1_3 left_pre right_pre retval PreH3 PreH14 PreH4 (by omega) PreH11
  exact quicksort_partition_combine_left_only_local l1_3 left_pre right_pre retval PreH14 (by omega) (by omega) hp PreH5

theorem proof_of_quicksort_range_return_wit_3_split_goal_2 : quicksort_range_return_wit_3_split_goal_2 := by
  unfold quicksort_range_return_wit_3_split_goal_2
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH10
    (same_outside_range_weaken_local l1_2 l1_3 left_pre (retval - 1) left_pre right_pre (by omega) (by omega) PreH4)

theorem proof_of_quicksort_range_return_wit_3_split_goal_3 : quicksort_range_return_wit_3_split_goal_3 := by
  unfold quicksort_range_return_wit_3_split_goal_3
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH9.trans PreH3

theorem proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3 := by
  unfold quicksort_range_return_wit_3
  right
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_3_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_3_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_3_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | trivial

theorem proof_of_quicksort_range_return_wit_4_split_goal_1 : quicksort_range_return_wit_4_split_goal_1 := by
  unfold quicksort_range_return_wit_4_split_goal_1
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro i j hi hij hj
  have he : i = j := by omega
  rw [he] <;> omega

theorem proof_of_quicksort_range_return_wit_4_split_goal_2 : quicksort_range_return_wit_4_split_goal_2 := by
  unfold quicksort_range_return_wit_4_split_goal_2
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact same_outside_range_refl l left_pre right_pre

theorem proof_of_quicksort_range_return_wit_4_split_goal_3 : quicksort_range_return_wit_4_split_goal_3 := by
  unfold quicksort_range_return_wit_4_split_goal_3
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact List.Perm.refl l

theorem proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4 := by
  unfold quicksort_range_return_wit_4
  right
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_4_split_goal_1 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_range_return_wit_4_split_goal_1 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_4_split_goal_2 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_range_return_wit_4_split_goal_2 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_4_split_goal_3 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_range_return_wit_4_split_goal_3 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | trivial

theorem proof_of_quicksort_return_wit_1_split_goal_1 : quicksort_return_wit_1_split_goal_1 := by
  unfold quicksort_return_wit_1_split_goal_1
  intro n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  apply range_nondecreasing_full_to_increasing
  simpa only [PreH1] using PreH4

theorem proof_of_quicksort_return_wit_1 : quicksort_return_wit_1 := by
  unfold quicksort_return_wit_1
  right
  intro n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_return_wit_1_split_goal_1 n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_return_wit_1_split_goal_1 n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | trivial

end SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_proof_manual
