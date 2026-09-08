import Algorithms.concatenating_numbers.lean.groundtruth.proof_lib
import Algorithms.concatenating_numbers.lean.groundtruth.concatenating_numbers_goal
import Algorithms.concatenating_numbers.lean.groundtruth.concatenating_numbers_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unusedVariables false
namespace Algorithms.concatenating_numbers.lean.groundtruth.concatenating_numbers_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.concatenating_numbers.lean.groundtruth.concatenating_numbers_goal Algorithms.concatenating_numbers.lean Algorithms.concatenating_numbers.lean.groundtruth.proof_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem cell_upper (count width row col : Int) (hw : 0≤width) (hr : row<count) (hc : col<width) :
    row*width+col<count*width := by
  have hm := Int.mul_le_mul_of_nonneg_right (show row+1≤count by omega) hw
  have he : (row+1)*width=row*width+width := by grind
  rw [he] at hm
  omega

theorem proof_of_quicksort_numbers_safety_wit_6_split_goal_1 : quicksort_numbers_safety_wit_6_split_goal_1 := by
  unfold quicksort_numbers_safety_wit_6_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1 lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH18.2.2 scan ⟨by omega,by omega⟩
  dump_pre_spatial
  change _≤2147483647
  omega

theorem proof_of_quicksort_numbers_safety_wit_6_split_goal_2 : quicksort_numbers_safety_wit_6_split_goal_2 := by
  unfold quicksort_numbers_safety_wit_6_split_goal_2
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1 lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH18.2.2 scan ⟨by omega,by omega⟩
  dump_pre_spatial
  change (-2147483648:Int)≤_
  omega

theorem proof_of_quicksort_numbers_safety_wit_6 : quicksort_numbers_safety_wit_6 := by
  unfold quicksort_numbers_safety_wit_6
  right
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1 lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_safety_wit_6_split_goal_1 high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1 lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))

    | (solve | Goal_apply (proof_of_quicksort_numbers_safety_wit_6_split_goal_2 high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1 lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))

    | trivial

theorem proof_of_quicksort_numbers_safety_wit_19_split_goal_1 : quicksort_numbers_safety_wit_19_split_goal_1 := by
  unfold quicksort_numbers_safety_wit_19_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  subst left_digit right_digit
  have hl := concat_left_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hr := concat_right_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  dump_pre_spatial
  change _≤2147483647
  omega

theorem proof_of_quicksort_numbers_safety_wit_19_split_goal_2 : quicksort_numbers_safety_wit_19_split_goal_2 := by
  unfold quicksort_numbers_safety_wit_19_split_goal_2
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  subst left_digit right_digit
  have hl := concat_left_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hr := concat_right_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  dump_pre_spatial
  change (-2147483648:Int)≤_
  omega

theorem proof_of_quicksort_numbers_safety_wit_19 : quicksort_numbers_safety_wit_19 := by
  unfold quicksort_numbers_safety_wit_19
  right
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_safety_wit_19_split_goal_1 high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))

    | (solve | Goal_apply (proof_of_quicksort_numbers_safety_wit_19_split_goal_2 high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_1 : quicksort_numbers_entail_wit_1 := by
  unfold quicksort_numbers_entail_wit_1
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hw := PreH14.2.2 high_pre ⟨by omega,by omega⟩
  have hlen : Zlength rows=Zlength lens := PreH14.1.trans PreH14.2.1.symm
  have hs := PartitionScanState_identity__partition_and_compare_init rows lens low_pre high_pre hlen
  Exists flat rows lens
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_2 : quicksort_numbers_entail_wit_2 := by
  unfold quicksort_numbers_entail_wit_2
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1_2 rows1_2 lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hw := PreH18.2.2 scan ⟨by omega,by omega⟩
  Exists flat1_2 rows1_2 lens1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact ConcatComparePrefix_zero__partition_and_compare_init rows1_2 lens1 scan high_pre
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_4_split_goal_1 : quicksort_numbers_entail_wit_4_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_4_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows flat1 rows1 position comparison total_length current_length lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  exact cell_upper count_pre number_width_pre scan position (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_4 : quicksort_numbers_entail_wit_4 := by
  unfold quicksort_numbers_entail_wit_4
  right
  intro high_pre low_pre number_width_pre count_pre lens rows flat1 rows1 position comparison total_length current_length lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_4_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows flat1 rows1 position comparison total_length current_length lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_6_split_goal_1 : quicksort_numbers_entail_wit_6_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_6_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows flat1 rows1 position comparison total_length current_length lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  exact cell_upper count_pre number_width_pre high_pre (position-current_length) (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_6 : quicksort_numbers_entail_wit_6 := by
  unfold quicksort_numbers_entail_wit_6
  right
  intro high_pre low_pre number_width_pre count_pre lens rows flat1 rows1 position comparison total_length current_length lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_6_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows flat1 rows1 position comparison total_length current_length lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_7_1 : quicksort_numbers_entail_wit_7_1 := by
  unfold quicksort_numbers_entail_wit_7_1
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1_2 position comparison total_length current_length lens1_2 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have hd : Znth (scan*number_width_pre+position) flat1 0=ConcatLeftDigit rows1_2 lens1_2 scan high_pre position := by
    rw [FlatRows_Znth__compare_left_digit flat1 rows1_2 count_pre number_width_pre scan position PreH52 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact (ConcatLeftDigit_first__compare_left_digit rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH48 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).symm
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_7_2 : quicksort_numbers_entail_wit_7_2 := by
  unfold quicksort_numbers_entail_wit_7_2
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1_2 position comparison total_length current_length lens1_2 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have hd : Znth (high_pre*number_width_pre+(position-current_length)) flat1 0=ConcatLeftDigit rows1_2 lens1_2 scan high_pre position := by
    rw [FlatRows_Znth__compare_left_digit flat1 rows1_2 count_pre number_width_pre high_pre (position-current_length) PreH50 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩,PreH37]
    exact (ConcatLeftDigit_second__compare_left_digit rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH46 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).symm
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_9_split_goal_1 : quicksort_numbers_entail_wit_9_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_9_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  exact cell_upper count_pre number_width_pre high_pre position (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_9 : quicksort_numbers_entail_wit_9 := by
  unfold quicksort_numbers_entail_wit_9
  right
  intro high_pre low_pre number_width_pre count_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_9_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_11_split_goal_1 : quicksort_numbers_entail_wit_11_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_11_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  exact cell_upper count_pre number_width_pre scan (position-pivot_length) (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_11 : quicksort_numbers_entail_wit_11 := by
  unfold quicksort_numbers_entail_wit_11
  right
  intro high_pre low_pre number_width_pre count_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_11_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows rows1 lens1 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_12_1 : quicksort_numbers_entail_wit_12_1 := by
  unfold quicksort_numbers_entail_wit_12_1
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1_2 lens1_2 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have hd := ConcatRightDigit_first_flat__compare_right_digit flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH54 PreH50 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_12_2 : quicksort_numbers_entail_wit_12_2 := by
  unfold quicksort_numbers_entail_wit_12_2
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1_2 lens1_2 flat1 boundary scan pivot_length current_length total_length comparison position left_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have hd := ConcatRightDigit_second_flat__compare_right_digit flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH52 PreH48 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega) (by omega)
  rw [←PreH37] at hd
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_13 : quicksort_numbers_entail_wit_13 := by
  unfold quicksort_numbers_entail_wit_13
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1_2 lens1_2 flat1_2 boundary scan pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hlen := concat_item_digits_Zlength__compare_outcome rows1_2 lens1_2 count_pre number_width_pre scan high_pre PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hc := ConcatComparePrefix_step__compare_outcome rows1_2 lens1_2 scan high_pre position PreH29 (by rw [←PreH25,←PreH26]; exact PreH1) (by rw [hlen]; omega)
  Exists flat1_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hc
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_14_1 : quicksort_numbers_entail_wit_14_1 := by
  unfold quicksort_numbers_entail_wit_14_1
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1_2 rows1_2 position comparison total_length current_length lens1_2 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hc := ConcatCompareOutcome_zero__compare_outcome rows1_2 lens1_2 scan high_pre position PreH27 (by
    rw [concat_item_digits_Zlength__compare_outcome rows1_2 lens1_2 count_pre number_width_pre scan high_pre PreH25 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    omega)
  sep_apply (store_int_undef_store_int naive_C_Rules (addr_notation (LE_var "position")) position)
  Exists flat1_2 rows1_2 lens1_2
  Intros_p hvalid0
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hc
    | (rw [PreH22]; exact hc)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_14_2 : quicksort_numbers_entail_wit_14_2 := by
  unfold quicksort_numbers_entail_wit_14_2
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1_2 lens1_2 flat1_2 boundary scan pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hc := ConcatCompareOutcome_difference__compare_outcome rows1_2 lens1_2 scan high_pre position PreH29 (by
    rw [concat_item_digits_Zlength__compare_outcome rows1_2 lens1_2 count_pre number_width_pre scan high_pre PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    omega) (by rw [←PreH25,←PreH26]; exact PreH1)
  rw [←PreH25,←PreH26] at hc
  sep_apply (store_int_undef_store_int naive_C_Rules (addr_notation (LE_var "position")) position)
  Exists flat1_2 rows1_2 lens1_2
  Intros_p hvalid0
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hc
    | (rw [PreH22]; exact hc)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_15 : quicksort_numbers_entail_wit_15 := by
  unfold quicksort_numbers_entail_wit_15
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1 lens1_2 flat1 boundary scan pivot_length current_length total_length comparison PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have he : boundary+1-1=boundary := by omega
  have hs := SwapRowsPrefix_zero__scan_row_swap rows1 lens1_2 count_pre number_width_pre (boundary+1) scan PreH22 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  repeat sep_apply (store_int_undef_store_int naive_C_Rules _ _)
  Exists flat1 rows1 rows1 lens1_2
  Intros_p hvalid0
  Intros_p hvalid1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hs
    | (rw [he]; exact PreH23)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_16_split_goal_1 : quicksort_numbers_entail_wit_16_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_16_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now comparison rows_before lens1 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  exact cell_upper count_pre number_width_pre boundary column (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_16 : quicksort_numbers_entail_wit_16 := by
  unfold quicksort_numbers_entail_wit_16
  right
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now comparison rows_before lens1 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_16_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now comparison rows_before lens1 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_17_split_goal_1 : quicksort_numbers_entail_wit_17_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_17_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now comparison rows_before lens1 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  exact cell_upper count_pre number_width_pre scan column (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_17 : quicksort_numbers_entail_wit_17 := by
  unfold quicksort_numbers_entail_wit_17
  right
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now comparison rows_before lens1 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_17_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now comparison rows_before lens1 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_18 : quicksort_numbers_entail_wit_18 := by
  unfold quicksort_numbers_entail_wit_18
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat_now_2 rows_now_2 comparison rows_before_2 lens1_2 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hb := PreH35.2.2 boundary ⟨by omega,by omega⟩
  have hs := PreH35.2.2 scan ⟨by omega,by omega⟩
  obtain ⟨rows_next,hflat,hswap⟩ := FlatRows_swap_progress_step__scan_row_swap flat_now_2 rows_before_2 rows_now_2 count_pre number_width_pre boundary scan column PreH41 PreH35.1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hb.1 hs.1 ⟨by omega,by omega⟩ PreH39
  Exists (replace_Znth (scan*number_width_pre+column) (Znth (boundary*number_width_pre+column) flat_now_2 0) (replace_Znth (boundary*number_width_pre+column) (Znth (scan*number_width_pre+column) flat_now_2 0) flat_now_2)) rows_next rows_before_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hflat
    | exact hswap
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_19_1 : quicksort_numbers_entail_wit_19_1 := by
  unfold quicksort_numbers_entail_wit_19_1
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat_now rows_now comparison rows_before lens1_2 pivot_length column scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hr := PreH19.1
  have hl := PreH19.2.1
  have he := SwapRowsPrefix_complete__scan_advance rows_before rows_now lens1_2 count_pre number_width_pre boundary scan column PreH19 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega) PreH23
  have hp := PartitionScanState_swap_advance__scan_advance rows rows_before lens lens1_2 count_pre number_width_pre low_pre high_pre boundary scan comparison PreH19 PreH20 PreH21 PreH22 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hw := RowsWellFormed_swap_Znth__scan_advance rows_before lens1_2 count_pre number_width_pre boundary scan PreH19 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  rw [←he] at hp hw
  have hsum : sum (swap_Znth 0 boundary scan lens1_2)=sum lens := by
    rw [sum_swap_Znth__pivot_finalization lens1_2 boundary scan ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact PreH24
  have hpivot : pivot_length=Znth high_pre (swap_Znth 0 boundary scan lens1_2) 0 := by
    rw [Znth_swap_Znth_diff__scan_advance Int 0 boundary scan high_pre lens1_2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega) (by omega)]
    exact PreH16
  sep_apply (store_int_undef_store_int naive_C_Rules (addr_notation (LE_var "comparison")) comparison)
  Exists flat_now rows_now (swap_Znth 0 boundary scan lens1_2)
  Intros_p hvalid0
  split_pure_spatial
  · unfold swap_Znth
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hp
    | exact hw
    | exact hsum
    | exact hpivot
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_19_2 : quicksort_numbers_entail_wit_19_2 := by
  unfold quicksort_numbers_entail_wit_19_2
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1_2 lens1_2 flat1_2 boundary scan pivot_length current_length total_length comparison PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hnot := ConcatCompareOutcome_nonpositive_not_item_before__scan_advance rows1_2 lens1_2 scan high_pre comparison PreH24 PreH1
  have hs := PartitionScanState_advance_nonbefore__scan_advance rows rows1_2 lens lens1_2 low_pre high_pre boundary scan PreH23 hnot
  repeat sep_apply (store_int_undef_store_int naive_C_Rules _ _)
  Exists flat1_2 rows1_2 lens1_2
  Intros_p hvalid0
  Intros_p hvalid1
  Intros_p hvalid2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_20 : quicksort_numbers_entail_wit_20 := by
  unfold quicksort_numbers_entail_wit_20
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows rows1_2 lens1_2 flat1_2 boundary scan pivot_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  Exists flat1_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_21 : quicksort_numbers_entail_wit_21 := by
  unfold quicksort_numbers_entail_wit_21
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat1 rows1 lens1_2 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hs : scan=high_pre := by omega
  subst scan
  have he : boundary+1-1=boundary := by omega
  have hz := SwapRowsPrefix_zero__scan_advance rows1 lens1_2 count_pre number_width_pre (boundary+1) high_pre PreH18 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  repeat sep_apply (store_int_undef_store_int naive_C_Rules _ _)
  Exists flat1 rows1 rows1 lens1_2
  Intros_p hvalid0
  Intros_p hvalid1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hz
    | (rw [he]; exact PreH19)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_22_split_goal_1 : quicksort_numbers_entail_wit_22_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_22_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now rows_before lens1 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  exact cell_upper count_pre number_width_pre pivot column (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_22 : quicksort_numbers_entail_wit_22 := by
  unfold quicksort_numbers_entail_wit_22
  right
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now rows_before lens1 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_22_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now rows_before lens1 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_23_split_goal_1 : quicksort_numbers_entail_wit_23_split_goal_1 := by
  unfold quicksort_numbers_entail_wit_23_split_goal_1
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now rows_before lens1 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  exact cell_upper count_pre number_width_pre high_pre column (by omega) (by omega) (by omega)

theorem proof_of_quicksort_numbers_entail_wit_23 : quicksort_numbers_entail_wit_23 := by
  unfold quicksort_numbers_entail_wit_23
  right
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now rows_before lens1 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_quicksort_numbers_entail_wit_23_split_goal_1 high_pre low_pre number_width_pre count_pre lens rows flat_now rows_now rows_before lens1 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))

    | trivial

theorem proof_of_quicksort_numbers_entail_wit_24 : quicksort_numbers_entail_wit_24 := by
  unfold quicksort_numbers_entail_wit_24
  right
  intro high_pre low_pre number_width_pre count_pre lens rows flat_now_2 rows_now_2 rows_before_2 lens1_2 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hp := PreH30.2.2 pivot ⟨by omega,by omega⟩
  have hh := PreH30.2.2 high_pre ⟨by omega,by omega⟩
  obtain ⟨rows_next,hflat,hswap⟩ := FlatRows_swap_progress_step__scan_row_swap flat_now_2 rows_before_2 rows_now_2 count_pre number_width_pre pivot high_pre column PreH34 PreH30.1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hp.1 hh.1 ⟨by omega,by omega⟩ PreH32
  Exists rows_next rows_before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hflat
    | exact hswap
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_entail_wit_25 : quicksort_numbers_entail_wit_25 := by
  unfold quicksort_numbers_entail_wit_25
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows flat_now rows_now rows_before lens1_2 pivot_length column pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hr := PreH18.1
  have hl := PreH18.2.1
  have hc : column=number_width_pre := by omega
  subst column
  have hpw := PreH18.2.2 pivot ⟨by omega,by omega⟩
  have hhw := PreH18.2.2 high_pre ⟨by omega,by omega⟩
  have he := SwapRowsPrefix_complete__pivot_finalization rows_before rows_now pivot high_pre number_width_pre hpw.1 hhw.1 PreH20
  let after := replace_Znth pivot pivot_length (replace_Znth high_pre (Znth pivot lens1_2 0) lens1_2)
  have hea : after=swap_Znth 0 pivot high_pre lens1_2 := by
    dsimp only [after]
    rw [PreH15]
    exact swap_Znth_reverse__pivot_finalization 0 pivot high_pre lens1_2 (by omega) (by omega)
  have hw := RowsWellFormed_swap__pivot_finalization rows_before lens1_2 count_pre number_width_pre pivot high_pre PreH18 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hp := PairedPermutation_swap__pivot_finalization rows rows_before lens lens1_2 pivot high_pre PreH19.1 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hs := SameOutsidePairedRange_swap_inside__pivot_finalization rows rows_before lens lens1_2 low_pre high_pre pivot high_pre PreH19.2.1 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hpart := PartitionScanState_finalize__pivot_finalization rows rows_before lens lens1_2 count_pre number_width_pre low_pre high_pre pivot PreH18 PreH19 (by omega) (by omega) (by omega) ⟨by omega,by omega⟩
  rw [←he,←hea] at hw hp hs hpart
  have hsum : sum after=sum lens := by
    rw [hea,sum_swap_Znth__pivot_finalization lens1_2 pivot high_pre ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact PreH21
  sep_apply (store_int_undef_store_int naive_C_Rules (addr_notation (LE_var "pivot_length")) pivot_length)
  Exists flat_now rows_now (replace_Znth pivot pivot_length (replace_Znth high_pre (Znth pivot lens1_2 0) lens1_2))
  Intros_p hvalid0
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hw
    | exact hp
    | exact hs
    | exact hpart
    | exact hsum
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_return_wit_1 : quicksort_numbers_return_wit_1 := by
  unfold quicksort_numbers_return_wit_1
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows pivot rows1_2 lens1_2 flat1_2 rows2 lens2 flat2 flat1_3 rows1_3 lens1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hpart2 := greedy_partitioned_preserved_left__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre low_pre high_pre pivot PreH8 PreH10 PreH11 (by omega) (by omega) PreH29
  have hpart3 := greedy_partitioned_preserved_right__quicksort_range_composition rows2 rows1_3 lens2 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 PreH3 PreH4 (by omega) (by omega) hpart2
  have hleft := greedy_sorted_range_preserved_outside__quicksort_range_composition rows2 rows1_3 lens2 lens1_3 (pivot+1) high_pre low_pre (pivot-1) PreH4 (by omega) (by have := PreH8.1; omega) (by intro k hk; exact Or.inl (by omega)) PreH12
  have hsorted := greedy_sorted_range_combine__quicksort_range_composition rows1_3 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 (by omega) (by omega) hpart3 hleft PreH5
  have hs12 := same_outside_paired_range_weaken__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 low_pre (pivot-1) low_pre high_pre (by omega) (by omega) PreH11
  have hs23 := same_outside_paired_range_weaken__quicksort_range_composition rows2 rows1_3 lens2 lens1_3 (pivot+1) high_pre low_pre high_pre (by omega) (by omega) PreH4
  have hs := same_outside_paired_range_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 low_pre high_pre PreH28
    (same_outside_paired_range_trans__quicksort_range_composition rows1_2 rows2 rows1_3 lens1_2 lens2 lens1_3 low_pre high_pre hs12 hs23)
  have hp := paired_permutation_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 PreH27
    (paired_permutation_trans__quicksort_range_composition rows1_2 rows2 rows1_3 lens1_2 lens2 lens1_3 PreH10 PreH3)
  Exists flat1_3 rows1_3 lens1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hsorted
    | exact hs
    | exact hp
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_return_wit_2 : quicksort_numbers_return_wit_2 := by
  unfold quicksort_numbers_return_wit_2
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows pivot rows1_2 lens1_2 flat1_2 rows2 lens2 flat2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hpart := greedy_partitioned_preserved_left__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre low_pre high_pre pivot PreH2 PreH4 PreH5 (by omega) (by omega) PreH23
  have hbase := greedy_sorted_range_base__quicksort_range_composition rows2 lens2 (pivot+1) high_pre (by omega)
  have hsorted := greedy_sorted_range_combine__quicksort_range_composition rows2 lens2 count_pre number_width_pre low_pre high_pre pivot PreH2 (by omega) (by omega) hpart PreH6 hbase
  have hchange := same_outside_paired_range_weaken__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 low_pre (pivot-1) low_pre high_pre (by omega) (by omega) PreH5
  have hs := same_outside_paired_range_trans__quicksort_range_composition rows rows1_2 rows2 lens lens1_2 lens2 low_pre high_pre PreH22 hchange
  have hp := paired_permutation_trans__quicksort_range_composition rows rows1_2 rows2 lens lens1_2 lens2 PreH21 PreH4
  Exists flat2 rows2 lens2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hsorted
    | exact hs
    | exact hp
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_return_wit_3 : quicksort_numbers_return_wit_3 := by
  unfold quicksort_numbers_return_wit_3
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre lens rows pivot rows1_2 lens1_2 flat1_2 flat1_3 rows1_3 lens1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hpart := greedy_partitioned_preserved_right__quicksort_range_composition rows1_2 rows1_3 lens1_2 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 PreH3 PreH4 (by omega) (by omega) PreH23
  have hbase := greedy_sorted_range_base__quicksort_range_composition rows1_3 lens1_3 low_pre (pivot-1) (by omega)
  have hsorted := greedy_sorted_range_combine__quicksort_range_composition rows1_3 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 (by omega) (by omega) hpart hbase PreH5
  have hchange := same_outside_paired_range_weaken__quicksort_range_composition rows1_2 rows1_3 lens1_2 lens1_3 (pivot+1) high_pre low_pre high_pre (by omega) (by omega) PreH4
  have hs := same_outside_paired_range_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 low_pre high_pre PreH22 hchange
  have hp := paired_permutation_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 PreH21 PreH3
  Exists flat1_3 rows1_3 lens1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hsorted
    | exact hs
    | exact hp
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_numbers_return_wit_4 : quicksort_numbers_return_wit_4 := by
  unfold quicksort_numbers_return_wit_4
  left
  intro high_pre low_pre number_width_pre count_pre lengths_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  Exists flat rows lens
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (apply greedy_sorted_range_base__quicksort_range_composition; omega)
    | exact same_outside_paired_range_refl__quicksort_range_composition rows lens low_pre high_pre
    | exact paired_permutation_refl__quicksort_range_composition rows lens (PreH13.1.trans PreH13.2.1.symm)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_entail_wit_1_1 : concatenating_numbers_entail_wit_1_1 := by
  unfold concatenating_numbers_entail_wit_1_1
  left
  intro result_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows flat1_2 rows1_2 lens1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs : GreedySorted rows1_2 lens1_2 := by
    intro i j hij
    apply PreH5 i j
    have hr := PreH1.1
    omega
  Exists flat1_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_entail_wit_1_2 : concatenating_numbers_entail_wit_1_2 := by
  unfold concatenating_numbers_entail_wit_1_2
  left
  intro result_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hc : count_pre=1 := by omega
  have hr := PreH8.1
  have hp := paired_permutation_refl__quicksort_range_composition rows lens (PreH8.1.trans PreH8.2.1.symm)
  have hs : GreedySorted rows lens := by
    intro i j hij
    have he : i=j := by omega
    subst j
    exact item_before_or_equal_refl__quicksort_range_composition rows lens i
  Exists flat rows lens
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hs
    | exact hp
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_entail_wit_2 : concatenating_numbers_entail_wit_2 := by
  unfold concatenating_numbers_entail_wit_2
  left
  intro result_pre lengths_pre number_width_pre count_pre numbers_pre lens rows rows1_2 lens1_2 flat1_2 result_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  subst result_length
  Exists flat1_2 ([] : List Int) rows1_2 lens1_2
  rw [ConcatenatedPrefix_zero__output_setup]
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg result_pre (sum lens))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.seg_empty result_pre 0 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_concatenating_numbers_entail_wit_3 : concatenating_numbers_entail_wit_3 := by
  unfold concatenating_numbers_entail_wit_3
  left
  intro result_pre lengths_pre number_width_pre count_pre numbers_pre lens rows flat1_2 result_length output_2 rows1_2 lens1_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hl := PreH10.2.2 i ⟨by omega,by omega⟩
  have ho : output_2=ConcatenatedOutputPrefix rows1_2 lens1_2 i 0 := by rw [ConcatenatedOutputPrefix_zero__output_setup]; exact PreH14
  Exists flat1_2 output_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact ho
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_entail_wit_4_split_goal_1 : concatenating_numbers_entail_wit_4_split_goal_1 := by
  unfold concatenating_numbers_entail_wit_4_split_goal_1
  intro number_width_pre count_pre lens rows flat1 result_length output rows1 lens1 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  exact cell_upper count_pre number_width_pre i j (by omega) (by omega) (by omega)

theorem proof_of_concatenating_numbers_entail_wit_4 : concatenating_numbers_entail_wit_4 := by
  unfold concatenating_numbers_entail_wit_4
  right
  intro number_width_pre count_pre lens rows flat1 result_length output rows1 lens1 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_entail_wit_4_split_goal_1 number_width_pre count_pre lens rows flat1 result_length output rows1 lens1 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32))

    | trivial

theorem proof_of_concatenating_numbers_entail_wit_5_split_goal_1 : concatenating_numbers_entail_wit_5_split_goal_1 := by
  unfold concatenating_numbers_entail_wit_5_split_goal_1
  intro number_width_pre count_pre lens rows flat1 result_length output rows1 lens1 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  rw [PreH31,PreH30,←PreH29]
  exact ConcatenatedOutputPrefix_lt_sum__output_inner_loop rows1 lens1 count_pre number_width_pre i j PreH26 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩

theorem proof_of_concatenating_numbers_entail_wit_5 : concatenating_numbers_entail_wit_5 := by
  unfold concatenating_numbers_entail_wit_5
  right
  intro number_width_pre count_pre lens rows flat1 result_length output rows1 lens1 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_entail_wit_5_split_goal_1 number_width_pre count_pre lens rows flat1 result_length output rows1 lens1 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34))

    | trivial

theorem proof_of_concatenating_numbers_entail_wit_6 : concatenating_numbers_entail_wit_6 := by
  unfold concatenating_numbers_entail_wit_6
  left
  intro result_pre lengths_pre number_width_pre count_pre numbers_pre lens rows flat1_2 result_length output_2 rows1_2 lens1_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  Exists flat1_2 (output_2++[Znth (i*number_width_pre+j) flat1_2 0]) rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (rw [Zlength_app,←PreH33]; simp only [Zlength_cons,Zlength_nil]; omega)
    | (rw [PreH32]; exact ConcatenatedOutputPrefix_append__output_inner_loop flat1_2 rows1_2 lens1_2 count_pre number_width_pre i j PreH36 PreH28 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_entail_wit_7 : concatenating_numbers_entail_wit_7 := by
  unfold concatenating_numbers_entail_wit_7
  left
  intro result_pre lengths_pre number_width_pre count_pre numbers_pre lens rows flat1_2 result_length output_2 rows1_2 lens1_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  Exists flat1_2 output_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (rw [PreH18,show j=Znth i lens1_2 0 by omega]; exact ConcatenatedOutputPrefix_full_row__output_inner_loop rows1_2 lens1_2 count_pre number_width_pre i PreH14 ⟨by omega,by omega⟩)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_return_wit_1 : concatenating_numbers_return_wit_1 := by
  unfold concatenating_numbers_return_wit_1
  left
  intro result_pre lengths_pre number_width_pre count_pre numbers_pre lens rows flat1_2 result_length output_2 rows1_2 lens1_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hi : i=count_pre := by omega
  have hout : output_2=concatenate_rows rows1_2 lens1_2 := by
    rw [PreH14,hi]
    exact ConcatenatedPrefix_full__largest_concatenation_final rows1_2 lens1_2 count_pre number_width_pre PreH10
  have hlen : Zlength output_2=sum lens := by
    rw [hout,RowsWellFormed_concatenate_rows_length__largest_concatenation_final rows1_2 lens1_2 count_pre number_width_pre PreH10]
    exact PreH13
  have hres : result_length=sum lens := by omega
  have hmax := GreedySorted_LargestConcatenation__largest_concatenation_final rows rows1_2 lens lens1_2 count_pre number_width_pre PreH10 PreH11 PreH12
  rw [←hout] at hmax
  Exists output_2 flat1_2 rows1_2 lens1_2
  rw [hres]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty result_pre (sum lens))).1)
  sep_apply (naive_C_Rules.IntArray.seg_to_full result_pre 0 (sum lens) output_2)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hmax | exact hlen | assumption | omega | rfl | trivial

end Algorithms.concatenating_numbers.lean.groundtruth.concatenating_numbers_proof_manual
