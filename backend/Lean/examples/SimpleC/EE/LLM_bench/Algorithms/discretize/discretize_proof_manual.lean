import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_goal
import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open discretize_goal discretize_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_partition_entail_wit_1 : partition_entail_wit_1 := by
  unfold partition_entail_wit_1
  left
  intro high_pre low_pre n_pre arr_pre l PreH1 PreH2 PreH3
  Exists l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_init__partition_scan l low_pre high_pre PreH1 PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1 := by
  unfold partition_entail_wit_2_1
  left
  intro high_pre low_pre n_pre arr_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  simp only [Zlength_replace_Znth] at hlen
  Exists (replace_Znth j (Znth (i+1) l1_2 0) (replace_Znth (i+1) (Znth j l1_2 0) l1_2))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_step_le__partition_scan l l1_2 low_pre high_pre pivot i j PreH4 PreH5 (by omega) PreH1 PreH2 PreH7 PreH8 PreH9 PreH10
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2 := by
  unfold partition_entail_wit_2_2
  left
  intro high_pre low_pre n_pre arr_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  Exists l1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_step_gt__partition_scan l l1_2 low_pre high_pre pivot i j PreH1 PreH2 PreH10
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_return_wit_1 : partition_return_wit_1 := by
  unfold partition_return_wit_1
  left
  intro high_pre low_pre n_pre arr_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  simp only [Zlength_replace_Znth] at hlen
  Exists (replace_Znth high_pre (Znth (i+1) l1_2 0) (replace_Znth (i+1) (Znth high_pre l1_2 0) l1_2))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact partition_scan_inv_final_permutation__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | exact partition_scan_inv_final_same_outside__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | exact partition_scan_inv_final_swap_partitioned_at__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1 := by
  unfold quicksort_range_return_wit_1
  left
  intro right_pre left_pre n_pre arr_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_4)
  Intros_p hlen
  have hlen34 := PreH2.1
  have hlen23 := PreH6.1
  have hp3 := partitioned_at_preserved_by_left__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH5 PreH16 PreH6 (by omega) PreH13
  have hp4 := partitioned_at_preserved_by_right__quicksort_range l1_3 l1_4 left_pre right_pre retval PreH1 PreH16 PreH2 (by omega) hp3
  have hleft : sorted_range l1_4 left_pre (retval-1) := by
    apply sorted_range_ext__quicksort_range l1_3 l1_4 left_pre (retval-1) PreH16 (by omega) hlen34 _ PreH7
    intro k hk
    exact PreH2.2 k (by omega) (Or.inl (by omega))
  have hs := sorted_range_from_both l1_4 left_pre right_pre retval ⟨PreH9,PreH10⟩ hp4 hleft PreH3
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 left_pre (retval-1) left_pre right_pre (by omega) (by omega) PreH6
  have hsame34 := same_outside_range_weaken__quicksort_range l1_3 l1_4 (retval+1) right_pre left_pre right_pre (by omega) (by omega) PreH2
  have hsame := same_outside_range_trans__quicksort_range l l1_3 l1_4 left_pre right_pre
    (same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH12 hsame23) hsame34
  Exists l1_4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact PreH11.trans (PreH5.trans PreH1)
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2 := by
  unfold quicksort_range_return_wit_2
  left
  intro right_pre left_pre n_pre arr_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_3)
  Intros_p hlen
  have hlen23 := PreH2.1
  have hp := partitioned_at_preserved_by_right__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH1 PreH13 PreH2 (by omega) PreH10
  have hs := sorted_range_from_right l1_3 left_pre right_pre retval PreH5 hp PreH3
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 (retval+1) right_pre left_pre right_pre (by omega) (by omega) PreH2
  have hsame := same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH9 hsame23
  Exists l1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact PreH8.trans PreH1
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3 := by
  unfold quicksort_range_return_wit_3
  left
  intro right_pre left_pre n_pre arr_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_3)
  Intros_p hlen
  have hlen23 := PreH3.1
  have hp := partitioned_at_preserved_by_left__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH2 PreH13 PreH3 (by omega) PreH10
  have hs := sorted_range_from_left l1_3 left_pre right_pre retval PreH1 hp PreH4
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 left_pre (retval-1) left_pre right_pre (by omega) (by omega) PreH3
  have hsame := same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH9 hsame23
  Exists l1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact PreH8.trans PreH2
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4 := by
  unfold quicksort_range_return_wit_4
  left
  intro right_pre left_pre n_pre arr_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  Exists l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact List.Perm.refl l
    | exact same_outside_range_refl__quicksort_range l left_pre right_pre
    | exact sorted_range_base l left_pre right_pre PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_int_array_quicksort_return_wit_1 : int_array_quicksort_return_wit_1 := by
  unfold int_array_quicksort_return_wit_1
  left
  intro n_pre arr_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_2)
  Intros_p hlen
  have hs := sorted_range_implies_increasing__quicksort_range l1_2 (by rw [hlen]; exact PreH3)
  Exists l1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_safety_wit_8 : discretize_safety_wit_8 := by
  unfold discretize_safety_wit_8
  left
  intro dest_map_pre n_pre src_pre src_l out_l slow PreH1 PreH2 PreH3 PreH4
  have hb := PreH4.2.2.2.1
  split_pures <;> dump_pre_spatial
  · change _≤2147483647
    omega
  · change (-2147483648:Int)≤_
    omega

theorem proof_of_discretize_entail_wit_1 : discretize_entail_wit_1 := by
  unfold discretize_entail_wit_1
  left
  intro dest_map_pre n_pre src_pre src_l PreH1 PreH2 PreH3
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg dest_map_pre n_pre)
  have he : sublist 0 0 src_l=[] := by simp [sublist]
  rw [he]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.full_empty dest_map_pre 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_2 : discretize_entail_wit_2 := by
  unfold discretize_entail_wit_2
  left
  intro dest_map_pre n_pre src_pre src_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  rw [sublist_split 0 (i+1) i src_l (by omega) (by omega),sublist_single 0 i src_l (by omega)]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_3 : discretize_entail_wit_3 := by
  unfold discretize_entail_wit_3
  left
  intro dest_map_pre n_pre src_pre src_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hi : i=n_pre := by omega
  subst i
  rw [sublist_self src_l n_pre PreH2.symm]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty dest_map_pre n_pre)).1)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_4 : discretize_entail_wit_4 := by
  unfold discretize_entail_wit_4
  left
  intro dest_map_pre n_pre src_pre src_l l1 PreH1 PreH2 PreH3 PreH4 PreH5
  Exists l1
  Exists l1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_init__discretize_dedup src_l l1 n_pre PreH1 PreH2 PreH3 PreH4
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_5_1 : discretize_entail_wit_5_1 := by
  unfold discretize_entail_wit_5_1
  left
  intro dest_map_pre n_pre src_pre src_l sorted_l_2 cur_l_2 fast slow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hlen := PreH10.1
  Exists sorted_l_2
  Exists (replace_Znth (slow+1) (Znth fast cur_l_2 0) cur_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_step_new__discretize_dedup src_l sorted_l_2 cur_l_2 slow fast PreH10 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_5_2 : discretize_entail_wit_5_2 := by
  unfold discretize_entail_wit_5_2
  left
  intro dest_map_pre n_pre src_pre src_l sorted_l_2 cur_l_2 fast slow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hlen := PreH10.1
  Exists sorted_l_2
  Exists cur_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_step_duplicate__discretize_dedup src_l sorted_l_2 cur_l_2 slow fast PreH10 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_6 : discretize_entail_wit_6 := by
  unfold discretize_entail_wit_6
  left
  intro dest_map_pre n_pre src_pre src_l sorted_l cur_l fast slow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hf : fast=n_pre := by omega
  subst fast
  Exists cur_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dedup_scan_inv_to_discretize_result__discretize_dedup src_l sorted_l cur_l slow n_pre PreH9 PreH2 PreH3
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_safety_wit_4 : query_forward_safety_wit_4 := by
  unfold query_forward_safety_wit_4
  left
  intro target_pre map_size_pre map_pre map_l high low PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hm := midpoint_between_bounds__query_forward_search low high PreH1
  split_pures <;> dump_pre_spatial
  · change _≤2147483647
    omega
  · change (-2147483648:Int)≤_
    omega

theorem proof_of_query_forward_entail_wit_1 : query_forward_entail_wit_1 := by
  unfold query_forward_entail_wit_1
  left
  intro target_pre map_size_pre map_pre map_l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_search_inv_init__query_forward_search map_l map_size_pre target_pre PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_2 : query_forward_entail_wit_2 := by
  unfold query_forward_entail_wit_2
  left
  intro target_pre map_size_pre map_pre map_l high low PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hm := midpoint_between_bounds__query_forward_search low high PreH1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_3_1 : query_forward_entail_wit_3_1 := by
  unfold query_forward_entail_wit_3_1
  left
  intro target_pre map_size_pre map_pre map_l low mid high PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_search_inv_step_right__query_forward_search map_l map_size_pre target_pre low mid high PreH3 PreH6 PreH11 PreH8 PreH9 PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_3_2 : query_forward_entail_wit_3_2 := by
  unfold query_forward_entail_wit_3_2
  left
  intro target_pre map_size_pre map_pre map_l low mid high PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_search_inv_step_left__query_forward_search map_l map_size_pre target_pre low mid high PreH3 PreH6 PreH11 PreH8 PreH9 PreH1 PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_4 : query_forward_entail_wit_4 := by
  unfold query_forward_entail_wit_4
  left
  intro target_pre map_size_pre map_pre map_l high low PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_result_not_found__query_forward_search map_l map_size_pre target_pre low high PreH9 PreH1 PreH7
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_return_wit_2 : query_forward_return_wit_2 := by
  unfold query_forward_return_wit_2
  left
  intro target_pre map_size_pre map_pre map_l low mid high PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact query_forward_result_found_unique__query_forward_search map_l map_size_pre target_pre mid PreH2 PreH5 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_proof_manual
