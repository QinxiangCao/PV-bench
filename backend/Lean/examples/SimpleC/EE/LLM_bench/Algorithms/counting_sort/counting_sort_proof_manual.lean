import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open counting_sort_goal counting_sort_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem nth_mem (l : List Int) (i : Int) (h : 0 ≤ i ∧ i < Zlength l) :
    Znth i l 0 ∈ l := by
  unfold Znth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [Zlength, Int.ofNat_eq_coe] at h; omega)]
  simp only [Option.getD_some]
  exact List.getElem_mem _

theorem proof_of_sort_entail_wit_1 : sort_entail_wit_1 := by
  unfold sort_entail_wit_1
  right
  intro n_pre input __default__App_option_Z PreH1 PreH2 PreH3 PreH4
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 100 (none : Option Int)) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 100 (none : Option Int)) ?_
  split_pure_spatial
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
      (intArray.undef_full_to_mixed_full (&("output")) 100)
      (intArray.undef_full_to_mixed_full (&("count")) 100)
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | decide
      | rfl
      | exact (fun k hk => Znth_repeat_lt __default__App_option_Z 100 k none hk)
      | exact (fun value hv => False.elim (by omega))


theorem proof_of_sort_entail_wit_2_split_goal_1 : sort_entail_wit_2_split_goal_1 := by
  unfold sort_entail_wit_2_split_goal_1
  intro n_pre input value count_mixed_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact counting_zeroed_prefix_replace__initial_zeroing count_mixed_2 value PreH6 ⟨PreH7, PreH1⟩ PreH11


theorem proof_of_sort_entail_wit_2_split_goal_2 : sort_entail_wit_2_split_goal_2 := by
  unfold sort_entail_wit_2_split_goal_2
  intro n_pre input value count_mixed_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simpa only [Zlength_replace_Znth] using PreH6


theorem proof_of_sort_entail_wit_2 : sort_entail_wit_2 := by
  unfold sort_entail_wit_2
  right
  intro n_pre input value count_mixed_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_2_split_goal_1 n_pre input value count_mixed_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_entail_wit_2_split_goal_2 n_pre input value count_mixed_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_sort_entail_wit_3 : sort_entail_wit_3 := by
  unfold sort_entail_wit_3
  right
  intro n_pre input value_2 count_mixed output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hm := counting_all_zero_materialization__initial_zeroing count_mixed PreH6
    (fun value hv => PreH11 value (by omega))
  subst count_mixed
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 100 (0 : Int)) ?_
  split_pure_spatial
  · exact intArray.mixed_full_to_full (&("count")) 100 (List.replicate 100 (0 : Int))
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | rfl
      | exact (fun value hv => Znth_repeat 0 100 value)
      | exact counting_histogram_empty__initial_zeroing input _ (fun value hv => Znth_repeat 0 100 value)


theorem proof_of_sort_entail_wit_4_split_goal_1 : sort_entail_wit_4_split_goal_1 := by
  unfold sort_entail_wit_4_split_goal_1
  intro n_pre input output_mixed_2 zeros __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH7


theorem proof_of_sort_entail_wit_4_split_goal_2 : sort_entail_wit_4_split_goal_2 := by
  unfold sort_entail_wit_4_split_goal_2
  intro n_pre input output_mixed_2 zeros __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  intro value hv
  rw [PreH8 value hv]
  omega


theorem proof_of_sort_entail_wit_4_split_goal_3 : sort_entail_wit_4_split_goal_3 := by
  unfold sort_entail_wit_4_split_goal_3
  intro n_pre input output_mixed_2 zeros __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH6


theorem proof_of_sort_entail_wit_4 : sort_entail_wit_4 := by
  unfold sort_entail_wit_4
  right
  intro n_pre input output_mixed_2 zeros __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_4_split_goal_1 n_pre input output_mixed_2 zeros __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_sort_entail_wit_4_split_goal_2 n_pre input output_mixed_2 zeros __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_sort_entail_wit_4_split_goal_3 n_pre input output_mixed_2 zeros __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9


theorem proof_of_sort_entail_wit_6_split_goal_1 : sort_entail_wit_6_split_goal_1 := by
  unfold sort_entail_wit_6_split_goal_1
  intro n_pre input i output_mixed_2 counts_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  intro bucket hb
  have hf := counting_frequency_prefix_snoc__histogram_cumulative input i bucket (by omega)
  by_cases he : Znth i input 0 = bucket
  · subst bucket
    rw [Znth_replace_Znth_Same 0 counts_2 _ _ (by omega), hf, PreH18 _ ⟨PreH1, PreH2⟩]
    simp
  · rw [Znth_replace_Znth_Diff 0 counts_2 _ bucket _ (by omega) (by omega) he, hf, PreH18 bucket hb]
    simp [he]


theorem proof_of_sort_entail_wit_6_split_goal_2 : sort_entail_wit_6_split_goal_2 := by
  unfold sort_entail_wit_6_split_goal_2
  intro n_pre input i output_mixed_2 counts_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simpa only [Zlength_replace_Znth] using PreH12


theorem proof_of_sort_entail_wit_6 : sort_entail_wit_6 := by
  unfold sort_entail_wit_6
  right
  intro n_pre input i output_mixed_2 counts_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_6_split_goal_1 n_pre input i output_mixed_2 counts_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_sort_entail_wit_6_split_goal_2 n_pre input i output_mixed_2 counts_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18


theorem proof_of_sort_entail_wit_7_split_goal_1 : sort_entail_wit_7_split_goal_1 := by
  unfold sort_entail_wit_7_split_goal_1
  intro n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : i = n_pre := by omega
  subst i
  intro bucket hb
  have hh := PreH12 bucket hb
  rw [sublist_self input n_pre PreH4.symm] at hh
  rw [hh]
  by_cases hb1 : bucket < 1
  · have he0 : bucket = 0 := by omega
    subst bucket
    simp only [show (0 : Int) < 1 by decide, if_pos]
    unfold CountingCumulativeEnd
    simp
  · rw [if_neg hb1]


theorem proof_of_sort_entail_wit_7_split_goal_2 : sort_entail_wit_7_split_goal_2 := by
  unfold sort_entail_wit_7_split_goal_2
  intro n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH11


theorem proof_of_sort_entail_wit_7_split_goal_3 : sort_entail_wit_7_split_goal_3 := by
  unfold sort_entail_wit_7_split_goal_3
  intro n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro _
  have he : i = n_pre := by omega
  subst i
  have hz := PreH12 0 (by omega)
  have ho := PreH12 1 (by omega)
  rw [sublist_self input n_pre PreH4.symm] at hz ho
  have hb := counting_cumulative_end_bound__histogram_cumulative input 1
  have hs := counting_cumulative_end_step__histogram_cumulative input 1 (by omega)
  have hzero : CountingCumulativeEnd input 0 = CountingFrequency input 0 := by simp [CountingCumulativeEnd]
  simp only [show (1 : Int) - 1 = 0 from rfl] at *
  omega


theorem proof_of_sort_entail_wit_7_split_goal_4 : sort_entail_wit_7_split_goal_4 := by
  unfold sort_entail_wit_7_split_goal_4
  intro n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro bucket hb
  have := PreH10 bucket hb
  omega


theorem proof_of_sort_entail_wit_7_split_goal_5 : sort_entail_wit_7_split_goal_5 := by
  unfold sort_entail_wit_7_split_goal_5
  intro n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH9


theorem proof_of_sort_entail_wit_7 : sort_entail_wit_7 := by
  unfold sort_entail_wit_7
  right
  intro n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_7_split_goal_1 n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sort_entail_wit_7_split_goal_2 n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sort_entail_wit_7_split_goal_3 n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sort_entail_wit_7_split_goal_4 n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sort_entail_wit_7_split_goal_5 n_pre input i counts output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12


theorem proof_of_sort_entail_wit_8_split_goal_1 : sort_entail_wit_8_split_goal_1 := by
  unfold sort_entail_wit_8_split_goal_1
  intro n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  intro bucket hb
  have hold := PreH13 bucket hb
  by_cases hlo : bucket < value
  · rw [Znth_replace_Znth_Diff 0 positions_2 value bucket _ (by omega) (by omega) (by omega), if_pos (by omega)]
    simpa only [if_pos hlo] using hold
  · by_cases he : bucket = value
    · subst bucket
      have hprev := PreH13 (value - 1) (by omega)
      rw [Znth_replace_Znth_Same 0 positions_2 value _ (by omega), if_pos (by omega)]
      rw [if_neg (by omega)] at hold
      rw [if_pos (by omega)] at hprev
      rw [hold, hprev, counting_cumulative_end_step__histogram_cumulative input value (by omega)]
      omega
    · rw [Znth_replace_Znth_Diff 0 positions_2 value bucket _ (by omega) (by omega) (Ne.symm he), if_neg (by omega)]
      simpa only [if_neg hlo] using hold


theorem proof_of_sort_entail_wit_8_split_goal_2 : sort_entail_wit_8_split_goal_2 := by
  unfold sort_entail_wit_8_split_goal_2
  intro n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  intro hnext
  rw [Znth_replace_Znth_Diff 0 positions_2 value (value + 1) _ (by omega) (by omega) (by omega)]
  rw [show value + 1 - 1 = value by omega, Znth_replace_Znth_Same 0 positions_2 value _ (by omega)]
  have hn := PreH13 (value + 1) (by omega)
  have hc := PreH13 value (by omega)
  have hp := PreH13 (value - 1) (by omega)
  rw [if_neg (by omega)] at hn hc
  rw [if_pos (by omega)] at hp
  rw [hn, hc, hp]
  have hb := counting_cumulative_end_bound__histogram_cumulative input (value + 1)
  rw [counting_cumulative_end_step__histogram_cumulative input (value + 1) (by omega),
    show value + 1 - 1 = value by omega, counting_cumulative_end_step__histogram_cumulative input value (by omega)] at hb
  omega


theorem proof_of_sort_entail_wit_8_split_goal_3 : sort_entail_wit_8_split_goal_3 := by
  unfold sort_entail_wit_8_split_goal_3
  intro n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simpa only [Zlength_replace_Znth] using PreH6


theorem proof_of_sort_entail_wit_8 : sort_entail_wit_8 := by
  unfold sort_entail_wit_8
  right
  intro n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_8_split_goal_1 n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sort_entail_wit_8_split_goal_2 n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sort_entail_wit_8_split_goal_3 n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13


theorem proof_of_sort_entail_wit_9 : sort_entail_wit_9 := by
  unfold sort_entail_wit_9
  right
  intro n_pre input value positions_2 output_mixed_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : value = 100 := by omega
  subst value
  have hinput := counting_index_bounds_to_In_bounds__placement_boundaries input (fun index hi => PreH9 index (by omega))
  obtain ⟨sorted, hlen, hbounds, hsorted⟩ := counting_canonical_sorted_exists__placement_boundaries input hinput
  have hplacement := counting_placement_initial__placement_boundaries input positions_2 output_mixed_2 sorted hsorted PreH13
  have hpositive : Zlength input - 1 ≥ 0 → 1 ≤ Znth (Znth (Zlength input - 1) input 0) positions_2 0 := by
    intro hn
    have hi : 0 ≤ Zlength input - 1 ∧ Zlength input - 1 < Zlength input := by omega
    have hv := PreH9 (Zlength input - 1) (by omega)
    rw [PreH13 _ hv, if_pos hv.2]
    exact counting_cumulative_positive_at_In__placement_boundaries input _ hv.1 (nth_mem input _ hi)
  Exists positions_2 sorted
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | exact (fun index hi => PreH12 index (by omega))


theorem proof_of_sort_entail_wit_10_split_goal_1 : sort_entail_wit_10_split_goal_1 := by
  unfold sort_entail_wit_10_split_goal_1
  intro n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact (PreH19 _ (PreH17 i ⟨PreH7, PreH16⟩)).2


theorem proof_of_sort_entail_wit_10_split_goal_2 : sort_entail_wit_10_split_goal_2 := by
  unfold sort_entail_wit_10_split_goal_2
  intro n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact (PreH17 i ⟨PreH7, PreH16⟩).2


theorem proof_of_sort_entail_wit_10_split_goal_3 : sort_entail_wit_10_split_goal_3 := by
  unfold sort_entail_wit_10_split_goal_3
  intro n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact (PreH17 i ⟨PreH7, PreH16⟩).1


theorem proof_of_sort_entail_wit_10 : sort_entail_wit_10 := by
  unfold sort_entail_wit_10
  right
  intro n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_10_split_goal_1 n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_sort_entail_wit_10_split_goal_2 n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_sort_entail_wit_10_split_goal_3 n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22


theorem proof_of_sort_entail_wit_11_split_goal_1 : sort_entail_wit_11_split_goal_1 := by
  unfold sort_entail_wit_11_split_goal_1
  intro n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rw [Znth_replace_Znth_Same 0 positions _ _ (by omega)]
  omega


theorem proof_of_sort_entail_wit_11_split_goal_2 : sort_entail_wit_11_split_goal_2 := by
  unfold sort_entail_wit_11_split_goal_2
  intro n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rw [Znth_replace_Znth_Same 0 positions _ _ (by omega)]
  omega


theorem proof_of_sort_entail_wit_11 : sort_entail_wit_11 := by
  unfold sort_entail_wit_11
  right
  intro n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_11_split_goal_1 n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
      | exact proof_of_sort_entail_wit_11_split_goal_2 n_pre input i output_mixed bucket_ends sorted positions __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26


theorem proof_of_sort_entail_wit_12 : sort_entail_wit_12 := by
  unfold sort_entail_wit_12
  right
  intro n_pre input i output_mixed_2 bucket_ends_2 sorted_2 positions_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hstep := counting_placement_step__placement_transition n_pre input i output_mixed_2 bucket_ends_2 sorted_2 positions_2
    __default__App_option_Z ⟨PreH12, PreH13⟩ PreH14 PreH15 PreH16 PreH18 ⟨PreH11, PreH20⟩ PreH21 PreH22 PreH23 PreH25 PreH7 PreH26
  obtain ⟨hpositions, hpositive, hsuffix, hprogress⟩ := hstep
  Exists bucket_ends_2 sorted_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | simpa only [Zlength_replace_Znth] using PreH16
      | simpa only [Zlength_replace_Znth] using PreH18
      | simpa only [PreH14] using PreH22
      | simpa only [PreH14] using hpositions
      | simpa only [PreH14] using hsuffix


theorem proof_of_sort_entail_wit_13 : sort_entail_wit_13 := by
  unfold sort_entail_wit_13
  right
  intro n_pre input i output_mixed bucket_ends positions sorted_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he : i = -1 := by omega
  subst i
  have hinput := counting_index_bounds_to_In_bounds__placement_boundaries input (fun index hi => PreH11 index (by omega))
  have hs := PreH16.1
  have hcomplete := counting_placement_complete__placement_boundaries input positions bucket_ends output_mixed sorted_2 hinput PreH16
  have hprefix := counting_output_prefix__placement_boundaries output_mixed sorted_2 n_pre (by omega) PreH5
    (fun index hi => hcomplete index (by omega))
  Exists sorted_2
  split_pure_spatial
  · sep_apply (intArray.mixed_full_split_to_mixed_seg (&("output")) n_pre 100 output_mixed ⟨PreH2, PreH3⟩)
    rw [hprefix]
    sep_apply (intArray.mixed_seg_to_seg (&("output")) 0 n_pre sorted_2)
    sep_apply (intArray.mixed_seg_to_undef_seg (&("output")) n_pre 100 (sublist n_pre 100 output_mixed))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption


theorem proof_of_sort_entail_wit_14_split_goal_1 : sort_entail_wit_14_split_goal_1 := by
  unfold sort_entail_wit_14_split_goal_1
  intro n_pre input sorted_2 bucket_starts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact counting_copy_initial__copyback input sorted_2


theorem proof_of_sort_entail_wit_14_split_goal_2 : sort_entail_wit_14_split_goal_2 := by
  unfold sort_entail_wit_14_split_goal_2
  intro n_pre input sorted_2 bucket_starts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact PreH6


theorem proof_of_sort_entail_wit_14 : sort_entail_wit_14 := by
  unfold sort_entail_wit_14
  right
  intro n_pre input sorted_2 bucket_starts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_14_split_goal_1 n_pre input sorted_2 bucket_starts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
      | exact proof_of_sort_entail_wit_14_split_goal_2 n_pre input sorted_2 bucket_starts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7


theorem proof_of_sort_entail_wit_15_split_goal_1 : sort_entail_wit_15_split_goal_1 := by
  unfold sort_entail_wit_15_split_goal_1
  intro n_pre input i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simp only [Int.sub_zero]
  exact counting_copy_step__copyback input sorted_2 live_2 i (by omega) (by omega) PreH12


theorem proof_of_sort_entail_wit_15_split_goal_2 : sort_entail_wit_15_split_goal_2 := by
  unfold sort_entail_wit_15_split_goal_2
  intro n_pre input i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simpa only [Zlength_replace_Znth] using PreH6


theorem proof_of_sort_entail_wit_15 : sort_entail_wit_15 := by
  unfold sort_entail_wit_15
  right
  intro n_pre input i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_15_split_goal_1 n_pre input i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_sort_entail_wit_15_split_goal_2 n_pre input i bucket_starts_2 live_2 sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12


theorem proof_of_sort_entail_wit_16_split_goal_1 : sort_entail_wit_16_split_goal_1 := by
  unfold sort_entail_wit_16_split_goal_1
  intro n_pre input i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : i = Zlength input := by omega
  rw [he] at PreH12
  have hlive := counting_copy_complete__copyback input sorted_2 live (by omega) PreH12
  rw [hlive]
  dump_pre_spatial
  exact PreH11


theorem proof_of_sort_entail_wit_16_split_goal_spatial : sort_entail_wit_16_split_goal_spatial := by
  unfold sort_entail_wit_16_split_goal_spatial
  intro n_pre input i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hout : intArray.seg (&("output")) 0 n_pre sorted_2 ** intArray.undef_seg (&("output")) n_pre 100
      |-- intArray.undef_full (&("output")) 100 := by
    refine naive_C_Rules.toContext.derivable1_trans _ _ _
      (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
        (intArray.seg_to_undef_seg (&("output")) 0 n_pre sorted_2)
        (naive_C_Rules.toContext.derivable1_refl _)) ?_
    simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using
      intArray.undef_seg_merge_to_undef_full (&("output")) 0 n_pre 100 ⟨PreH2, PreH3⟩
  refine naive_C_Rules.toContext.derivable1_trans _
    ((intArray.seg (&("output")) 0 n_pre sorted_2 ** intArray.undef_seg (&("output")) n_pre 100) **
      intArray.full (&("count")) 100 bucket_starts) _ ?_ ?_
  · cancel
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ hout
      (intArray.full_to_undef_full (&("count")) 100 bucket_starts)


theorem proof_of_sort_entail_wit_16 : sort_entail_wit_16 := by
  unfold sort_entail_wit_16
  right
  intro n_pre input i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · exact proof_of_sort_entail_wit_16_split_goal_spatial n_pre input i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_sort_entail_wit_16_split_goal_1 n_pre input i bucket_starts live sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12


theorem proof_of_sort_return_wit_1_split_goal_1 : sort_return_wit_1_split_goal_1 := by
  unfold sort_return_wit_1_split_goal_1
  intro n_pre input sorted PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH5.2


theorem proof_of_sort_return_wit_1_split_goal_2 : sort_return_wit_1_split_goal_2 := by
  unfold sort_return_wit_1_split_goal_2
  intro n_pre input sorted PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH5.1


theorem proof_of_sort_return_wit_1 : sort_return_wit_1 := by
  unfold sort_return_wit_1
  right
  intro n_pre input sorted PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_return_wit_1_split_goal_1 n_pre input sorted PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_return_wit_1_split_goal_2 n_pre input sorted PreH1 PreH2 PreH3 PreH4 PreH5

end SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_proof_manual
