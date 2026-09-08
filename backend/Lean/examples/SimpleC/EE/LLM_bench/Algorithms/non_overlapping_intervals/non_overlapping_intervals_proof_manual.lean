import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_goal
import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open non_overlapping_intervals_goal non_overlapping_intervals_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_swap_intervals_return_wit_1 : swap_intervals_return_wit_1 := by
  unfold swap_intervals_return_wit_1
  left
  intro j_pre i_pre ed_pre st_pre ps ed_l st_l n PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  let stnew := replace_Znth j_pre (Znth i_pre st_l 0) (replace_Znth i_pre (Znth j_pre st_l 0) st_l)
  let ednew := replace_Znth j_pre (Znth i_pre ed_l 0) (replace_Znth i_pre (Znth j_pre ed_l 0) ed_l)
  prop_apply (intArray.full_Zlength st_pre n stnew)
  Intros_p hst
  change Zlength stnew = n at hst
  change Zlength (replace_Znth j_pre (Znth i_pre st_l 0) (replace_Znth i_pre (Znth j_pre st_l 0) st_l)) = n at hst
  rw [Zlength_replace_Znth, Zlength_replace_Znth] at hst
  have hps := PreH5.2.1
  have hi : 0 ≤ i_pre ∧ i_pre < Zlength ps := ⟨PreH1, by omega⟩
  have hj : 0 ≤ j_pre ∧ j_pre < Zlength ps := ⟨PreH3, by omega⟩
  have hpair := pair_intervals_swap__swap_records st_l ed_l ps i_pre j_pre PreH5 ⟨PreH1, by omega⟩ ⟨PreH3, by omega⟩
  have hbound := interval_swap_bounds__swap_records ps i_pre j_pre hi hj PreH6
  have hperm := interval_swap_permutation__swap_records ps i_pre j_pre hi hj
  have hswap : IntervalSwappedAt ps (interval_swap ps i_pre j_pre) i_pre j_pre := rfl
  refine Automation.exp_right_rule (CRules := naive_C_Rules) stnew ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ednew ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (interval_swap ps i_pre j_pre) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_partition_intervals_entail_wit_1 : partition_intervals_entail_wit_1 := by
  unfold partition_intervals_entail_wit_1
  right
  intro high_pre low_pre intervalsSize_pre ps ed_l st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hs := lomuto_scan_init__partition_lomuto st_l ed_l ps low_pre high_pre PreH6 PreH3 PreH4 (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_partition_intervals_entail_wit_2_1 : partition_intervals_entail_wit_2_1 := by
  unfold partition_intervals_entail_wit_2_1
  right
  intro high_pre low_pre intervalsSize_pre ps pivot_end_2 j_2 i_2 st1_2 ed1_2 ps1_2 st1_3 ed1_3 ps1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hl := PreH18.2.1
  have hn := PreH3.2.1
  have hfields := (pair_intervals_lengths_and_fields__partition_lomuto st1_2 ed1_2 ps1_2 PreH18).2.2 j_2 ⟨by omega, by omega⟩
  have hguard : interval_end (Znth j_2 ps1_2 default_interval) ≤ pivot_end_2 := by rw [hfields.2]; exact PreH7
  have hnext := lomuto_scan_accept__partition_lomuto ps ps1_2 ps1_3 low_pre high_pre i_2 j_2 pivot_end_2
    PreH9 PreH10 (by omega) PreH12 PreH13 PreH8 PreH20 PreH5 PreH6 hguard
  have hfnew := (pair_intervals_lengths_and_fields__partition_lomuto st1_3 ed1_3 ps1_3 PreH3).2.2 high_pre ⟨by omega, by omega⟩
  have hpiv := hnext.2.2.1
  rw [hfnew.2] at hpiv
  have heq : Znth high_pre ed1_2 0 = Znth high_pre ed1_3 0 := by omega
  rw [← hpiv] at hnext
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1_3 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_partition_intervals_entail_wit_2_2 : partition_intervals_entail_wit_2_2 := by
  unfold partition_intervals_entail_wit_2_2
  right
  intro high_pre low_pre intervalsSize_pre ps pivot_end_2 j_2 i_2 st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hfields := (pair_intervals_lengths_and_fields__partition_lomuto st1_2 ed1_2 ps1_2 PreH12).2.2 j_2 ⟨by omega, by omega⟩
  have hguard : pivot_end_2 < interval_end (Znth j_2 ps1_2 default_interval) := by rw [hfields.2]; exact PreH1
  have hnext := lomuto_scan_skip__partition_lomuto ps ps1_2 low_pre high_pre i_2 j_2 pivot_end_2 PreH2 PreH14 hguard
  rw [PreH11] at hnext
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_partition_intervals_return_wit_1 : partition_intervals_return_wit_1 := by
  unfold partition_intervals_return_wit_1
  right
  intro high_pre low_pre intervalsSize_pre ps pivot_end j i st1_2 ed1_2 ps1_2 st1_3 ed1_3 ps1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hl := PreH15.2.1
  obtain ⟨hperm,hsame,hpart⟩ := lomuto_scan_finish__partition_lomuto ps ps1_2 ps1_3 low_pre high_pre i j pivot_end
    PreH6 PreH7 (by omega) PreH9 PreH10 PreH11 PreH5 PreH17 PreH3 PreH4
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1_3 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_quicksort_intervals_range_entail_wit_1_1 : quicksort_intervals_range_entail_wit_1_1 := by
  unfold quicksort_intervals_range_entail_wit_1_1
  left
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps ed_l st_l retval st1 ed1 ps1 st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH1.2.1
  have hsame := PreH4.1
  have hperm : IntervalPermutation ps ps1_2 := PreH11.trans PreH3
  have hout := outside_range_compose_nested__quicksort_left ps ps1 ps1_2 left_pre right_pre (retval-1) PreH12 PreH4 (by omega)
  have hpart := partition_preserved_by_left_sort__quicksort_left ps1 ps1_2 left_pre right_pre retval PreH3 PreH4 PreH16 (by omega) PreH13
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ed1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_quicksort_intervals_range_entail_wit_1_2 : quicksort_intervals_range_entail_wit_1_2 := by
  unfold quicksort_intervals_range_entail_wit_1_2
  right
  intro right_pre left_pre intervalsSize_pre ps ed_l st_l retval st1 ed1 ps1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hsorted := sorted_range_empty__quicksort_left ps1 left_pre (retval-1) (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_quicksort_intervals_range_return_wit_1 : quicksort_intervals_range_return_wit_1 := by
  unfold quicksort_intervals_range_return_wit_1
  left
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps pivot current_st current_ed current_ps st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH1.2.1
  have hsame := PreH4.1
  have hpart := right_sort_preserves_left_partition__quicksort_finish current_ps ps1_2 left_pre right_pre pivot
    PreH3 PreH4 PreH8 PreH12 (by omega) PreH17
  have hleft := sorted_range_preserved_on_left__quicksort_finish current_ps ps1_2 left_pre right_pre pivot
    PreH4 PreH8 PreH12 (by omega) PreH18
  have hsorted := partition_merge_sorted_ranges__quicksort_finish ps1_2 left_pre right_pre pivot hpart hleft PreH5
  have hperm : IntervalPermutation ps ps1_2 := PreH15.trans PreH3
  have hout := outside_range_compose_nested__quicksort_finish ps current_ps ps1_2 left_pre (pivot+1) right_pre (by omega) PreH16 PreH4
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ed1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_quicksort_intervals_range_return_wit_2 : quicksort_intervals_range_return_wit_2 := by
  unfold quicksort_intervals_range_return_wit_2
  right
  intro right_pre left_pre intervalsSize_pre ps pivot current_st current_ed current_ps PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hright := sorted_range_trivial__quicksort_finish current_ps (pivot+1) right_pre (by omega)
  have hsorted := partition_merge_sorted_ranges__quicksort_finish current_ps left_pre right_pre pivot PreH12 PreH13 hright
  refine Automation.exp_right_rule (CRules := naive_C_Rules) current_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_quicksort_intervals_range_return_wit_3 : quicksort_intervals_range_return_wit_3 := by
  unfold quicksort_intervals_range_return_wit_3
  right
  intro right_pre left_pre intervalsSize_pre ps ed_l st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hout := same_outside_refl__quicksort_finish ps left_pre right_pre
  have hsorted := sorted_range_trivial__quicksort_finish ps left_pre right_pre PreH1
  have hperm : IntervalPermutation ps ps := List.Perm.refl _
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_quicksort_intervals_return_wit_1 : quicksort_intervals_return_wit_1 := by
  unfold quicksort_intervals_return_wit_1
  left
  intro intervalsSize_pre ed_pre st_pre ps ed_l st_l st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH1.2.1
  have hsorted := sorted_full_range__quicksort_finish ps1_2 intervalsSize_pre (by omega) PreH5
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ed1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_eraseOverlapIntervals_entail_wit_1 : eraseOverlapIntervals_entail_wit_1 := by
  unfold eraseOverlapIntervals_entail_wit_1
  right
  intro intervalsSize_pre ps ed_l st_l st1 ed1 ps1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hl := PreH4.2.1
  have hsize : 0 < Zlength ps1 := by omega
  obtain ⟨hstart,hend,hlo,hproper,hup⟩ := pair_intervals_fields_at__greedy_prefix st1 ed1 ps1 0 PreH4 PreH5 ⟨le_refl _,hsize⟩
  have hg := greedy_prefix_singleton__greedy_prefix ps1 hsize
  rw [← hend] at hg
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_eraseOverlapIntervals_entail_wit_2_1 : eraseOverlapIntervals_entail_wit_2_1 := by
  unfold eraseOverlapIntervals_entail_wit_2_1
  right
  intro intervalsSize_pre ps sorted_ps_2 sorted_ed_2 sorted_st_2 last_end_2 kept_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hl := PreH11.2.1
  have hi : 0 ≤ i_2 ∧ i_2 < Zlength sorted_ps_2 := ⟨by omega, by omega⟩
  obtain ⟨hstart,hend,hlo,hproper,hup⟩ := pair_intervals_fields_at__greedy_prefix sorted_st_2 sorted_ed_2 sorted_ps_2 i_2 PreH11 PreH12 hi
  have hg := greedy_prefix_accept__greedy_prefix sorted_ps_2 i_2 kept_2 last_end_2 hi PreH12 PreH15 (by rw [← hstart]; exact PreH1)
  rw [← hend] at hg
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_eraseOverlapIntervals_entail_wit_2_2 : eraseOverlapIntervals_entail_wit_2_2 := by
  unfold eraseOverlapIntervals_entail_wit_2_2
  right
  intro intervalsSize_pre ps sorted_ps_2 sorted_ed_2 sorted_st_2 last_end_2 kept_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hl := PreH11.2.1
  have hi : 0 ≤ i_2 ∧ i_2 < Zlength sorted_ps_2 := ⟨by omega, by omega⟩
  obtain ⟨hstart,hend,hlo,hproper,hup⟩ := pair_intervals_fields_at__greedy_prefix sorted_st_2 sorted_ed_2 sorted_ps_2 i_2 PreH11 PreH12 hi
  have hg := greedy_prefix_skip__greedy_prefix sorted_ps_2 i_2 kept_2 last_end_2 hi PreH12 PreH14 PreH15 (by rw [← hstart]; exact PreH1)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_eraseOverlapIntervals_entail_wit_3 : eraseOverlapIntervals_entail_wit_3 := by
  unfold eraseOverlapIntervals_entail_wit_3
  right
  intro intervalsSize_pre ps sorted_ps_2 sorted_ed_2 sorted_st_2 last_end kept i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hl := PreH10.2.1
  have hplen : Zlength ps = Zlength sorted_ps_2 := by
    change (ps.length : Int) = (sorted_ps_2.length : Int)
    rw [PreH12.length_eq]
  have hg : GreedyPrefixState sorted_ps_2 (Zlength ps) kept last_end := by
    have he : Zlength ps = i := by omega
    rw [he]; exact PreH14
  have hminimum := greedy_prefix_yields_minimum_removals__optimum_returns ps sorted_ps_2 kept last_end hplen PreH12 hg
  have hfinal : GreedyPrefixState sorted_ps_2 (Zlength sorted_st_2) kept last_end := by
    have he : Zlength sorted_st_2 = i := by omega
    rw [he]; exact PreH14
  rw [hplen,hl] at hminimum
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_eraseOverlapIntervals_return_wit_1 : eraseOverlapIntervals_return_wit_1 := by
  unfold eraseOverlapIntervals_return_wit_1
  right
  intro intervalsSize_pre ps sorted_st sorted_ed sorted_ps kept last_end PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_eraseOverlapIntervals_return_wit_2 : eraseOverlapIntervals_return_wit_2 := by
  unfold eraseOverlapIntervals_return_wit_2
  left
  intro intervalsSize_pre ed_pre st_pre ps ed_l st_l st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH2.2.1
  have hplen : Zlength ps = Zlength ps1_2 := by
    change (ps.length : Int) = (ps1_2.length : Int)
    rw [PreH4.length_eq]
  have hmin := minimum_removals_empty__optimum_returns ps (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ed1_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps1_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

end SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_proof_manual
