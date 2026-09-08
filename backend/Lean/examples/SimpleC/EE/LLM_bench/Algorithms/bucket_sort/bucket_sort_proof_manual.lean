import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open bucket_sort_goal bucket_sort_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_sort_safety_wit_17_split_goal_1 : sort_safety_wit_17_split_goal_1 := by
  unfold sort_safety_wit_17_split_goal_1
  intro n_pre a_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH26 (Z.rem (Z.quot (Znth i current 0) exponent) 10) ⟨PreH1, PreH2⟩
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega


theorem proof_of_sort_safety_wit_17_split_goal_2 : sort_safety_wit_17_split_goal_2 := by
  unfold sort_safety_wit_17_split_goal_2
  intro n_pre a_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH26 (Z.rem (Z.quot (Znth i current 0) exponent) 10) ⟨PreH1, PreH2⟩
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega


theorem proof_of_sort_safety_wit_17 : sort_safety_wit_17 := by
  unfold sort_safety_wit_17
  right
  intro n_pre a_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  all_goals first
    | exact proof_of_sort_safety_wit_17_split_goal_1 n_pre a_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_sort_safety_wit_17_split_goal_2 n_pre a_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30


theorem proof_of_sort_safety_wit_21_split_goal_1 : sort_safety_wit_21_split_goal_1 := by
  unfold sort_safety_wit_21_split_goal_1
  intro n_pre a_pre input digit exponent max_value totals histogram current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hb := PreH18 digit (by omega)
  have hp := PreH18 (digit - 1) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega


theorem proof_of_sort_safety_wit_21_split_goal_2 : sort_safety_wit_21_split_goal_2 := by
  unfold sort_safety_wit_21_split_goal_2
  intro n_pre a_pre input digit exponent max_value totals histogram current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hb := PreH18 digit (by omega)
  have hp := PreH18 (digit - 1) (by omega)
  dump_pre_spatial
  simp only [INT_MAX, INT_MIN]
  omega


theorem proof_of_sort_safety_wit_21 : sort_safety_wit_21 := by
  unfold sort_safety_wit_21
  right
  intro n_pre a_pre input digit exponent max_value totals histogram current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures
  all_goals first
    | exact proof_of_sort_safety_wit_21_split_goal_1 n_pre a_pre input digit exponent max_value totals histogram current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_sort_safety_wit_21_split_goal_2 n_pre a_pre input digit exponent max_value totals histogram current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23


theorem proof_of_sort_entail_wit_1_split_goal_1 : sort_entail_wit_1_split_goal_1 := by
  unfold sort_entail_wit_1_split_goal_1
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  refine ⟨⟨0, by omega, rfl⟩, ?_⟩
  intro index hi
  have he : index = 0 := by omega
  subst index
  omega


theorem proof_of_sort_entail_wit_1_split_goal_2 : sort_entail_wit_1_split_goal_2 := by
  unfold sort_entail_wit_1_split_goal_2
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH5


theorem proof_of_sort_entail_wit_1_split_goal_3 : sort_entail_wit_1_split_goal_3 := by
  unfold sort_entail_wit_1_split_goal_3
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  exact (PreH5 0 (by omega)).2


theorem proof_of_sort_entail_wit_1_split_goal_4 : sort_entail_wit_1_split_goal_4 := by
  unfold sort_entail_wit_1_split_goal_4
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  exact (PreH5 0 (by omega)).1


theorem proof_of_sort_entail_wit_1 : sort_entail_wit_1 := by
  unfold sort_entail_wit_1
  right
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_1_split_goal_1 n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_entail_wit_1_split_goal_2 n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_entail_wit_1_split_goal_3 n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_entail_wit_1_split_goal_4 n_pre input PreH1 PreH2 PreH3 PreH4 PreH5


theorem proof_of_sort_entail_wit_2_1_split_goal_1 : sort_entail_wit_2_1_split_goal_1 := by
  unfold sort_entail_wit_2_1_split_goal_1
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact prefix_maximum_extend_greater__maximum_pass_entry input i max_value (by omega) PreH11 PreH1


theorem proof_of_sort_entail_wit_2_1_split_goal_2 : sort_entail_wit_2_1_split_goal_2 := by
  unfold sort_entail_wit_2_1_split_goal_2
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact (PreH10 i (by omega)).2


theorem proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1 := by
  unfold sort_entail_wit_2_1
  right
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_2_1_split_goal_1 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_sort_entail_wit_2_1_split_goal_2 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_sort_entail_wit_2_2_split_goal_1 : sort_entail_wit_2_2_split_goal_1 := by
  unfold sort_entail_wit_2_2_split_goal_1
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact prefix_maximum_extend_bounded__maximum_pass_entry input i max_value PreH11 PreH1


theorem proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2 := by
  unfold sort_entail_wit_2_2
  right
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_2_2_split_goal_1 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_sort_entail_wit_3_split_goal_1 : sort_entail_wit_3_split_goal_1 := by
  unfold sort_entail_wit_3_split_goal_1
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine ⟨List.Perm.refl _, ?_⟩
  intro left right hr
  simp only [Z.modulo, Int.fmod_one]
  omega


theorem proof_of_sort_entail_wit_3_split_goal_2 : sort_entail_wit_3_split_goal_2 := by
  unfold sort_entail_wit_3_split_goal_2
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact ⟨0, by decide, rfl⟩


theorem proof_of_sort_entail_wit_3_split_goal_3 : sort_entail_wit_3_split_goal_3 := by
  unfold sort_entail_wit_3_split_goal_3
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have he : i = n_pre := by omega
  simpa only [he] using PreH10


theorem proof_of_sort_entail_wit_3_split_goal_4 : sort_entail_wit_3_split_goal_4 := by
  unfold sort_entail_wit_3_split_goal_4
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact PreH9


theorem proof_of_sort_entail_wit_3_split_goal_5 : sort_entail_wit_3_split_goal_5 := by
  unfold sort_entail_wit_3_split_goal_5
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact PreH9


theorem proof_of_sort_entail_wit_3 : sort_entail_wit_3 := by
  unfold sort_entail_wit_3
  right
  intro n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_3_split_goal_1 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_entail_wit_3_split_goal_2 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_entail_wit_3_split_goal_3 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_entail_wit_3_split_goal_4 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_sort_entail_wit_3_split_goal_5 n_pre input max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10


theorem proof_of_sort_entail_wit_4_split_goal_1 : sort_entail_wit_4_split_goal_1 := by
  unfold sort_entail_wit_4_split_goal_1
  intro n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  intro k hk
  omega


theorem proof_of_sort_entail_wit_4_split_goal_2 : sort_entail_wit_4_split_goal_2 := by
  unfold sort_entail_wit_4_split_goal_2
  intro n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH11


theorem proof_of_sort_entail_wit_4_split_goal_3 : sort_entail_wit_4_split_goal_3 := by
  unfold sort_entail_wit_4_split_goal_3
  intro n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH10


theorem proof_of_sort_entail_wit_4_split_goal_4 : sort_entail_wit_4_split_goal_4 := by
  unfold sort_entail_wit_4_split_goal_4
  intro n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact decimal_exponent_active_bound__maximum_pass_entry exponent max_value PreH13 PreH6 PreH7 PreH1


theorem proof_of_sort_entail_wit_4_split_goal_5 : sort_entail_wit_4_split_goal_5 := by
  unfold sort_entail_wit_4_split_goal_5
  intro n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  rfl


theorem proof_of_sort_entail_wit_4 : sort_entail_wit_4 := by
  unfold sort_entail_wit_4
  right
  intro n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_4_split_goal_1 n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_sort_entail_wit_4_split_goal_2 n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_sort_entail_wit_4_split_goal_3 n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_sort_entail_wit_4_split_goal_4 n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_sort_entail_wit_4_split_goal_5 n_pre input exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14


theorem proof_of_sort_entail_wit_5_split_goal_1 : sort_entail_wit_5_split_goal_1 := by
  unfold sort_entail_wit_5_split_goal_1
  intro n_pre input exponent max_value digit zero_prefix_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_app, Zlength_cons, Zlength_nil, PreH6]
  omega


theorem proof_of_sort_entail_wit_5 : sort_entail_wit_5 := by
  unfold sort_entail_wit_5
  right
  intro n_pre input exponent max_value digit zero_prefix_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_5_split_goal_1 n_pre input exponent max_value digit zero_prefix_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19


theorem proof_of_sort_entail_wit_6 : sort_entail_wit_6 := by
  unfold sort_entail_wit_6
  right
  intro n_pre input exponent max_value digit_2 zero_prefix current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have he : digit_2 = 10 := by omega
  rw [he] at PreH6 PreH16 ⊢
  have hz := digit_histogram_prefix_zero__count_zero_init current_2 exponent zero_prefix PreH16
  Exists zero_prefix
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full (&("count")) 0 10 zero_prefix
  · split_pures <;> dump_pre_spatial
    all_goals assumption


theorem proof_of_sort_entail_wit_7_split_goal_1 : sort_entail_wit_7_split_goal_1 := by
  unfold sort_entail_wit_7_split_goal_1
  intro n_pre input current_2 counts_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro digit hd
  rw [PreH13 digit hd]
  omega


theorem proof_of_sort_entail_wit_7_split_goal_2 : sort_entail_wit_7_split_goal_2 := by
  unfold sort_entail_wit_7_split_goal_2
  intro n_pre input current_2 counts_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH12


theorem proof_of_sort_entail_wit_7_split_goal_3 : sort_entail_wit_7_split_goal_3 := by
  unfold sort_entail_wit_7_split_goal_3
  intro n_pre input current_2 counts_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH11


theorem proof_of_sort_entail_wit_7 : sort_entail_wit_7 := by
  unfold sort_entail_wit_7
  right
  intro n_pre input current_2 counts_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_7_split_goal_1 n_pre input current_2 counts_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_sort_entail_wit_7_split_goal_2 n_pre input current_2 counts_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_sort_entail_wit_7_split_goal_3 n_pre input current_2 counts_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17


theorem proof_of_sort_entail_wit_8_split_goal_1 : sort_entail_wit_8_split_goal_1 := by
  unfold sort_entail_wit_8_split_goal_1
  intro n_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact (c_radix_digit_range__stable_placement _ exponent (PreH25 i (by omega)).1 (by omega)).2


theorem proof_of_sort_entail_wit_8_split_goal_2 : sort_entail_wit_8_split_goal_2 := by
  unfold sort_entail_wit_8_split_goal_2
  intro n_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact (c_radix_digit_range__stable_placement _ exponent (PreH25 i (by omega)).1 (by omega)).1


theorem proof_of_sort_entail_wit_8 : sort_entail_wit_8 := by
  unfold sort_entail_wit_8
  right
  intro n_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_8_split_goal_1 n_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | exact proof_of_sort_entail_wit_8_split_goal_2 n_pre input i exponent max_value counts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30


theorem proof_of_sort_entail_wit_9_split_goal_1 : sort_entail_wit_9_split_goal_1 := by
  unfold sort_entail_wit_9_split_goal_1
  intro n_pre input i exponent max_value counts_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := radix_digit_c_bridge__stable_placement _ exponent (PreH25 i (by omega)).1 (by omega)
  rw [← hb] at PreH1 PreH2 ⊢
  exact digit_histogram_prefix_step__histogram_update current_2 exponent i counts_2 (by omega) PreH16 ⟨PreH1, PreH2⟩ PreH30


theorem proof_of_sort_entail_wit_9_split_goal_2 : sort_entail_wit_9_split_goal_2 := by
  unfold sort_entail_wit_9_split_goal_2
  intro n_pre input i exponent max_value counts_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  simpa only [Zlength_replace_Znth] using PreH16


theorem proof_of_sort_entail_wit_9 : sort_entail_wit_9 := by
  unfold sort_entail_wit_9
  right
  intro n_pre input i exponent max_value counts_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_9_split_goal_1 n_pre input i exponent max_value counts_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
      | exact proof_of_sort_entail_wit_9_split_goal_2 n_pre input i exponent max_value counts_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30


theorem proof_of_sort_entail_wit_10_split_goal_1 : sort_entail_wit_10_split_goal_1 := by
  unfold sort_entail_wit_10_split_goal_1
  intro n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have he : i = n_pre := by omega
  simpa only [he] using PreH20


theorem proof_of_sort_entail_wit_10_split_goal_2 : sort_entail_wit_10_split_goal_2 := by
  unfold sort_entail_wit_10_split_goal_2
  intro n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro digit hd
  have := PreH16 digit hd
  omega


theorem proof_of_sort_entail_wit_10_split_goal_3 : sort_entail_wit_10_split_goal_3 := by
  unfold sort_entail_wit_10_split_goal_3
  intro n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH15


theorem proof_of_sort_entail_wit_10_split_goal_4 : sort_entail_wit_10_split_goal_4 := by
  unfold sort_entail_wit_10_split_goal_4
  intro n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH14


theorem proof_of_sort_entail_wit_10 : sort_entail_wit_10 := by
  unfold sort_entail_wit_10
  right
  intro n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_10_split_goal_1 n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_sort_entail_wit_10_split_goal_2 n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_sort_entail_wit_10_split_goal_3 n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_sort_entail_wit_10_split_goal_4 n_pre input i exponent max_value counts current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20


theorem proof_of_sort_entail_wit_11 : sort_entail_wit_11 := by
  unfold sort_entail_wit_11
  right
  intro n_pre input current_2 histogram_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have ht := digit_prefix_totals_init__prefix_totals histogram_2 PreH5
  Exists histogram_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | simpa only [PreH3] using PreH13 | simpa only [PreH3] using PreH17


theorem proof_of_sort_entail_wit_12 : sort_entail_wit_12 := by
  unfold sort_entail_wit_12
  right
  intro n_pre input digit exponent max_value totals_2 histogram_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hstep := digit_prefix_totals_step__prefix_totals histogram_2 totals_2 digit PreH6 PreH7 (by omega) PreH23
  have hmass := digit_histogram_prefix_mass_bound__prefix_totals current_2 exponent n_pre histogram_2 digit (by omega) PreH6 PreH22 (by omega)
  have hbound : ∀ index, 0 ≤ index ∧ index < 10 → 0 ≤ Znth index (replace_Znth digit (Znth digit totals_2 0 + Znth (digit - 1) totals_2 0) totals_2) 0 ∧ Znth index (replace_Znth digit (Znth digit totals_2 0 + Znth (digit - 1) totals_2 0) totals_2) 0 ≤ n_pre := by
    intro index hi
    by_cases he : index = digit
    · subst index
      rw [(hstep digit (by omega)).1 (by omega)]
      exact hmass
    · rw [Znth_replace_Znth_Diff 0 totals_2 digit index _ (by omega) (by omega) (Ne.symm he)]
      exact PreH18 index hi
  Exists histogram_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | simpa only [Zlength_replace_Znth] using PreH7 | simpa only [PreH4] using PreH17 | simpa only [PreH4] using PreH22 | simpa only [PreH4] using hbound


theorem proof_of_sort_entail_wit_13 : sort_entail_wit_13 := by
  unfold sort_entail_wit_13
  right
  intro n_pre input digit_2 exponent max_value totals histogram_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have he : digit_2 = 10 := by omega
  rw [he] at PreH23
  have hbound : ∀ digit, 0 ≤ digit ∧ digit < 10 → ((0 ≤ Znth digit histogram_2 0 ∧ Znth digit histogram_2 0 ≤ Zlength input) ∧ 0 ≤ Znth digit totals 0) ∧ Znth digit totals 0 ≤ Zlength input := by
    intro digit hd
    have hh := PreH17 digit hd
    have ht := PreH18 digit hd
    exact ⟨⟨⟨hh.1, by omega⟩, ht.1⟩, by omega⟩
  Exists histogram_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | simpa only [PreH4] using PreH22


theorem proof_of_sort_entail_wit_14 : sort_entail_wit_14 := by
  unfold sort_entail_wit_14
  right
  intro n_pre input current_2 histogram_2 endpoints max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram_2 := by simpa only [PreH4] using PreH18
  have hprogress := bucket_placement_initial__stable_placement current_2 exponent histogram_2 endpoints PreH5 PreH6 hhist PreH19
  have hlen : Zlength (List.replicate 1000 (none : Option Int)) = 1000 := by rw [Zlength, List.length_replicate]; rfl
  have hcurrent : ∀ k, 0 ≤ k ∧ k < n_pre → ((0 ≤ Znth k current_2 0 ∧ Znth k current_2 0 ≤ 999999999) ∧ 0 ≤ Z.rem (Z.quot (Znth k current_2 0) exponent) 10) ∧ Z.rem (Z.quot (Znth k current_2 0) exponent) 10 < 10 := by
    intro k hk
    have hv := PreH13 k hk
    have hd := c_radix_digit_range__stable_placement _ exponent hv.1 (by omega)
    exact ⟨⟨hv, hd.1⟩, hd.2⟩
  have hcounters : ∀ k, 0 ≤ k ∧ k ≤ n_pre - 1 → 1 ≤ Znth (Z.rem (Z.quot (Znth k current_2 0) exponent) 10) endpoints 0 ∧ Znth (Z.rem (Z.quot (Znth k current_2 0) exponent) 10) endpoints 0 ≤ n_pre := by
    intro k hk
    have hd := hcurrent k (by omega)
    have hb := radix_digit_c_bridge__stable_placement _ exponent hd.1.1.1 (by omega)
    have hp := bucket_progress_counter_for_index__stable_placement current_2 exponent (Zlength current_2) histogram_2 endpoints (List.replicate 1000 none) k PreH5 hhist hprogress (by omega) (by omega) (by rw [hb]; exact ⟨hd.1.2, hd.2⟩)
    rw [hb] at hp
    exact ⟨hp, (PreH14 _ ⟨hd.1.2, hd.2⟩).2⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 1000 (none : Option Int)) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) histogram_2 ?_
  split_pure_spatial
  · exact intArray.undef_full_to_mixed_full (&("output")) 1000
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | simpa only [PreH4, Int.sub_add_cancel] using hprogress


theorem proof_of_sort_entail_wit_15_split_goal_1 : sort_entail_wit_15_split_goal_1 := by
  unfold sort_entail_wit_15_split_goal_1
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact (PreH29 i (by omega)).2


theorem proof_of_sort_entail_wit_15_split_goal_2 : sort_entail_wit_15_split_goal_2 := by
  unfold sort_entail_wit_15_split_goal_2
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact (PreH29 i (by omega)).1


theorem proof_of_sort_entail_wit_15_split_goal_3 : sort_entail_wit_15_split_goal_3 := by
  unfold sort_entail_wit_15_split_goal_3
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact (PreH27 i (by omega)).2


theorem proof_of_sort_entail_wit_15_split_goal_4 : sort_entail_wit_15_split_goal_4 := by
  unfold sort_entail_wit_15_split_goal_4
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact (PreH27 i (by omega)).1.2


theorem proof_of_sort_entail_wit_15 : sort_entail_wit_15 := by
  unfold sort_entail_wit_15
  right
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_15_split_goal_1 n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
      | exact proof_of_sort_entail_wit_15_split_goal_2 n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
      | exact proof_of_sort_entail_wit_15_split_goal_3 n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
      | exact proof_of_sort_entail_wit_15_split_goal_4 n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34


theorem proof_of_sort_entail_wit_16_split_goal_1 : sort_entail_wit_16_split_goal_1 := by
  unfold sort_entail_wit_16_split_goal_1
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  rw [Znth_replace_Znth_Same 0 counters _ _ (by omega)]
  omega


theorem proof_of_sort_entail_wit_16_split_goal_2 : sort_entail_wit_16_split_goal_2 := by
  unfold sort_entail_wit_16_split_goal_2
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  rw [Znth_replace_Znth_Same 0 counters _ _ (by omega)]
  omega


theorem proof_of_sort_entail_wit_16 : sort_entail_wit_16 := by
  unfold sort_entail_wit_16
  right
  intro n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_16_split_goal_1 n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
      | exact proof_of_sort_entail_wit_16_split_goal_2 n_pre input i exponent max_value mixed_output histogram current counters PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38


theorem proof_of_sort_entail_wit_17 : sort_entail_wit_17 := by
  unfold sort_entail_wit_17
  right
  intro n_pre input i exponent max_value mixed_output_2 histogram_2 current_2 counters_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hb := radix_digit_c_bridge__stable_placement _ exponent (PreH31 i (by omega)).1.1.1 (by omega)
  have hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram_2 := by simpa only [PreH19] using PreH37
  have hstep := bucket_placement_step__stable_placement current_2 exponent histogram_2 counters_2 mixed_output_2 i PreH20 PreH21 (by omega) (by rw [hb]; exact ⟨PreH7, PreH8⟩) hhist PreH38 (by simpa only [hb] using And.intro PreH1 PreH2)
  simp only [hb] at hstep
  let digit := Z.rem (Z.quot (Znth i current_2 0) exponent) 10
  let next := replace_Znth digit (Znth digit counters_2 0 - 1) counters_2
  have hbound : ∀ d, 0 ≤ d ∧ d < 10 → 0 ≤ Znth d next 0 ∧ Znth d next 0 ≤ n_pre := by
    intro d hd
    change 0 ≤ Znth d (replace_Znth digit (Znth digit counters_2 0 - 1) counters_2) 0 ∧ Znth d (replace_Znth digit (Znth digit counters_2 0 - 1) counters_2) 0 ≤ n_pre
    by_cases he : d = digit
    · subst d
      rw [Znth_replace_Znth_Same 0 counters_2 digit _ (by change 0 ≤ Z.rem (Z.quot (Znth i current_2 0) exponent) 10 ∧ Z.rem (Z.quot (Znth i current_2 0) exponent) 10 < Zlength counters_2; omega)]
      change 0 ≤ Znth (Z.rem (Z.quot (Znth i current_2 0) exponent) 10) counters_2 0 - 1 ∧ Znth (Z.rem (Z.quot (Znth i current_2 0) exponent) 10) counters_2 0 - 1 ≤ n_pre
      omega
    · rw [Znth_replace_Znth_Diff 0 counters_2 digit d _ (by change 0 ≤ Z.rem (Z.quot (Znth i current_2 0) exponent) 10 ∧ Z.rem (Z.quot (Znth i current_2 0) exponent) 10 < Zlength counters_2; omega) (by omega) (Ne.symm he)]
      exact ⟨(PreH32 d hd).1.2, (PreH32 d hd).2⟩
  have hcombined : ∀ d, 0 ≤ d ∧ d < 10 → ((0 ≤ Znth d histogram_2 0 ∧ Znth d histogram_2 0 ≤ Zlength input) ∧ 0 ≤ Znth d next 0) ∧ Znth d next 0 ≤ Zlength input := by
    intro d hd
    have hh := (PreH32 d hd).1.1
    have hn := hbound d hd
    exact ⟨⟨⟨hh.1, by omega⟩, hn.1⟩, by omega⟩
  have hremaining : ∀ k, 0 ≤ k ∧ k ≤ i - 1 → 1 ≤ Znth (Z.rem (Z.quot (Znth k current_2 0) exponent) 10) next 0 ∧ Znth (Z.rem (Z.quot (Znth k current_2 0) exponent) 10) next 0 ≤ Zlength input := by
    intro k hk
    have hv := PreH31 k (by omega)
    have hbridge := radix_digit_c_bridge__stable_placement _ exponent hv.1.1.1 (by omega)
    have hp := bucket_progress_counter_for_index__stable_placement current_2 exponent i histogram_2 next _ k PreH20 hhist hstep (by omega) (by omega) (by rw [hbridge]; exact ⟨hv.1.2, hv.2⟩)
    rw [hbridge] at hp
    exact ⟨hp, by have := (hbound _ ⟨hv.1.2, hv.2⟩).2; omega⟩
  Exists histogram_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | simpa only [Zlength_replace_Znth] using PreH21 | simpa only [Zlength_replace_Znth] using PreH22 | simpa only [PreH18] using PreH37 | simpa only [Int.sub_add_cancel] using hstep


theorem proof_of_sort_entail_wit_18 : sort_entail_wit_18 := by
  unfold sort_entail_wit_18
  right
  intro n_pre input i exponent max_value mixed_output counters histogram_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have he : i = -1 := by omega
  subst i
  have hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram_2 := by simpa only [PreH5] using PreH23
  have hvalues : ∀ k, 0 ≤ k ∧ k < Zlength current_2 → (0 ≤ Znth k current_2 0 ∧ Znth k current_2 0 ≤ 999999999) ∧ 0 ≤ RadixDigit (Znth k current_2 0) exponent ∧ RadixDigit (Znth k current_2 0) exponent < 10 := by
    intro k hk
    have hv := PreH17 k (by omega)
    rw [radix_digit_c_bridge__stable_placement _ exponent hv.1.1.1 (by omega)]
    exact ⟨hv.1.1, hv.1.2, hv.2⟩
  have hcomplete := bucket_placement_complete__stable_placement current_2 exponent histogram_2 counters mixed_output PreH6 (by omega) hhist (fun k hk => (hvalues k hk).2) PreH24
  have hprops := radix_stable_output_properties__stable_placement current_2 exponent 0 999999999 hvalues
  have hlen : Zlength (RadixStableOutput current_2 exponent) = n_pre := by omega
  have hpass : StableDigitPass current_2 (RadixStableOutput current_2 exponent) exponent := rfl
  have hcombined : ∀ k, 0 ≤ k ∧ k < n_pre → ((0 ≤ Znth k current_2 0 ∧ Znth k current_2 0 ≤ 999999999) ∧ 0 ≤ Znth k (RadixStableOutput current_2 exponent) 0) ∧ Znth k (RadixStableOutput current_2 exponent) 0 ≤ 999999999 := by
    intro k hk
    have hv := PreH17 k hk
    have ho := hprops.2.2 k (by omega)
    exact ⟨⟨hv.1.1, ho.1⟩, ho.2⟩
  Exists (RadixStableOutput current_2 exponent) histogram_2
  split_pure_spatial
  · sep_apply (intArray.mixed_full_split_to_mixed_seg (&("output")) n_pre 1000 mixed_output (by omega))
    have hp : sublist 0 n_pre mixed_output = List.map some (RadixStableOutput current_2 exponent) := by simpa only [PreH5] using hcomplete.2
    rw [hp]
    sep_apply (intArray.mixed_seg_to_seg (&("output")) 0 n_pre (RadixStableOutput current_2 exponent))
    sep_apply (intArray.mixed_seg_to_undef_seg (&("output")) n_pre 1000 (sublist n_pre 1000 mixed_output))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption


theorem proof_of_sort_entail_wit_19 : sort_entail_wit_19 := by
  unfold sort_entail_wit_19
  right
  intro n_pre input current_2 histogram bucket_starts_2 pass_output_2 max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hc := radix_copy_prefix_zero__copy_back current_2 pass_output_2
  have hcombined : ∀ k, 0 ≤ k ∧ k < Zlength input → ((((0 ≤ Znth k current_2 0 ∧ Znth k current_2 0 ≤ 999999999) ∧ 0 ≤ Znth k pass_output_2 0) ∧ Znth k pass_output_2 0 ≤ 999999999) ∧ 0 ≤ Znth k current_2 0) ∧ Znth k current_2 0 ≤ 999999999 := by
    intro k hk
    have hv := PreH14 k (by omega)
    exact ⟨⟨hv, hv.1.1.1⟩, hv.1.1.2⟩
  Exists current_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega


theorem proof_of_sort_entail_wit_20 : sort_entail_wit_20 := by
  unfold sort_entail_wit_20
  right
  intro n_pre input i exponent max_value working_2 pass_output_2 bucket_starts_2 current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  simp only [Int.sub_zero]
  have hcopy := radix_copy_prefix_step__copy_back current_2 pass_output_2 working_2 i (by omega) (by omega) PreH22
  have hcombined : ∀ k, 0 ≤ k ∧ k < Zlength input → ((((0 ≤ Znth k current_2 0 ∧ Znth k current_2 0 ≤ 999999999) ∧ 0 ≤ Znth k pass_output_2 0) ∧ Znth k pass_output_2 0 ≤ 999999999) ∧ 0 ≤ Znth k (replace_Znth i (Znth i pass_output_2 0) working_2) 0) ∧ Znth k (replace_Znth i (Znth i pass_output_2 0) working_2) 0 ≤ 999999999 := by
    intro k hk
    have hv := PreH17 k (by omega)
    by_cases he : k = i
    · subst k
      rw [Znth_replace_Znth_Same 0 working_2 i _ (by omega)]
      exact ⟨⟨hv.1.1, hv.1.1.1.2⟩, hv.1.1.2⟩
    · rw [Znth_replace_Znth_Diff 0 working_2 i k _ (by omega) (by omega) (Ne.symm he)]
      exact hv
  Exists current_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | simpa only [Zlength_replace_Znth, PreH8, PreH4]


theorem proof_of_sort_entail_wit_21_split_goal_1 : sort_entail_wit_21_split_goal_1 := by
  unfold sort_entail_wit_21_split_goal_1
  intro n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  have he : working = pass_output_2 := by
    apply (ListLib.list_eq_ext working pass_output_2 0).mpr
    constructor
    · change Zlength working = Zlength pass_output_2
      omega
    · change ∀ index, 0 ≤ index ∧ index < Zlength working → Znth index working 0 = Znth index pass_output_2 0
      intro index hi
      exact PreH22.1 index (by omega)
  rw [he]
  exact ⟨PreH20.1.trans (stable_digit_pass_permutation__pass_transition current pass_output_2 exponent PreH21), stable_digit_pass_next_order__pass_transition current pass_output_2 exponent (by omega) PreH20.2 PreH21⟩


theorem proof_of_sort_entail_wit_21_split_goal_2 : sort_entail_wit_21_split_goal_2 := by
  unfold sort_entail_wit_21_split_goal_2
  intro n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  exact decimal_exponent_next__pass_transition exponent PreH19 PreH12


theorem proof_of_sort_entail_wit_21_split_goal_3 : sort_entail_wit_21_split_goal_3 := by
  unfold sort_entail_wit_21_split_goal_3
  intro n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  intro k hk
  have hv := PreH17 k hk
  exact ⟨hv.1.2, hv.2⟩


theorem proof_of_sort_entail_wit_21_split_goal_4 : sort_entail_wit_21_split_goal_4 := by
  unfold sort_entail_wit_21_split_goal_4
  intro n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  exact PreH16


theorem proof_of_sort_entail_wit_21_split_goal_spatial : sort_entail_wit_21_split_goal_spatial := by
  unfold sort_entail_wit_21_split_goal_spatial
  intro n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hout : intArray.seg (&("output")) 0 n_pre pass_output_2 ** intArray.undef_seg (&("output")) n_pre 1000 |-- intArray.undef_full (&("output")) 1000 := by
    refine naive_C_Rules.toContext.derivable1_trans _ (intArray.undef_seg (&("output")) 0 n_pre ** intArray.undef_seg (&("output")) n_pre 1000) _ ?_ ?_
    · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ (intArray.seg_to_undef_seg (&("output")) 0 n_pre pass_output_2) (naive_C_Rules.toContext.derivable1_refl _)
    · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.undef_seg_merge_to_undef_full (&("output")) 0 n_pre 1000 (by omega)
  refine naive_C_Rules.toContext.derivable1_trans _ ((intArray.seg (&("output")) 0 n_pre pass_output_2 ** intArray.undef_seg (&("output")) n_pre 1000) ** intArray.full (&("count")) 10 bucket_starts) _ ?_ ?_
  · cancel
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ hout (intArray.full_to_undef_full (&("count")) 10 bucket_starts)


theorem proof_of_sort_entail_wit_21 : sort_entail_wit_21 := by
  unfold sort_entail_wit_21
  right
  intro n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · exact proof_of_sort_entail_wit_21_split_goal_spatial n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  · split_pures
    all_goals first
      | exact proof_of_sort_entail_wit_21_split_goal_1 n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_sort_entail_wit_21_split_goal_2 n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_sort_entail_wit_21_split_goal_3 n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_sort_entail_wit_21_split_goal_4 n_pre input i exponent max_value working pass_output_2 bucket_starts current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22


theorem proof_of_sort_entail_wit_22_split_goal_1 : sort_entail_wit_22_split_goal_1 := by
  unfold sort_entail_wit_22_split_goal_1
  intro n_pre input pass_output max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH13


theorem proof_of_sort_entail_wit_22_split_goal_2 : sort_entail_wit_22_split_goal_2 := by
  unfold sort_entail_wit_22_split_goal_2
  intro n_pre input pass_output max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH12


theorem proof_of_sort_entail_wit_22 : sort_entail_wit_22 := by
  unfold sort_entail_wit_22
  right
  intro n_pre input pass_output max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_22_split_goal_1 n_pre input pass_output max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_sort_entail_wit_22_split_goal_2 n_pre input pass_output max_value exponent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_sort_entail_wit_23_split_goal_1 : sort_entail_wit_23_split_goal_1 := by
  unfold sort_entail_wit_23_split_goal_1
  intro n_pre input exponent max_value current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact radix_pass_state_final_increasing__final_result input current n_pre exponent max_value PreH4 PreH5 (by omega) PreH6 PreH1 (fun index hi => (PreH11 index hi).1) PreH12 PreH14


theorem proof_of_sort_entail_wit_23_split_goal_2 : sort_entail_wit_23_split_goal_2 := by
  unfold sort_entail_wit_23_split_goal_2
  intro n_pre input exponent max_value current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH14.1


theorem proof_of_sort_entail_wit_23_split_goal_3 : sort_entail_wit_23_split_goal_3 := by
  unfold sort_entail_wit_23_split_goal_3
  intro n_pre input exponent max_value current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH10


theorem proof_of_sort_entail_wit_23 : sort_entail_wit_23 := by
  unfold sort_entail_wit_23
  right
  intro n_pre input exponent max_value current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_entail_wit_23_split_goal_1 n_pre input exponent max_value current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_sort_entail_wit_23_split_goal_2 n_pre input exponent max_value current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_sort_entail_wit_23_split_goal_3 n_pre input exponent max_value current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14


theorem proof_of_sort_return_wit_1_split_goal_1 : sort_return_wit_1_split_goal_1 := by
  unfold sort_return_wit_1_split_goal_1
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  exact increasing_short_list__final_result input (by omega)


theorem proof_of_sort_return_wit_1_split_goal_2 : sort_return_wit_1_split_goal_2 := by
  unfold sort_return_wit_1_split_goal_2
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  exact List.Perm.refl _


theorem proof_of_sort_return_wit_1 : sort_return_wit_1 := by
  unfold sort_return_wit_1
  right
  intro n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_sort_return_wit_1_split_goal_1 n_pre input PreH1 PreH2 PreH3 PreH4 PreH5
      | exact proof_of_sort_return_wit_1_split_goal_2 n_pre input PreH1 PreH2 PreH3 PreH4 PreH5

end SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_proof_manual
