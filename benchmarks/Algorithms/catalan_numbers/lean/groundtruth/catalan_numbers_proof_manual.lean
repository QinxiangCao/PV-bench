import Algorithms.catalan_numbers.lean.groundtruth.catalan_numbers_goal
import Algorithms.catalan_numbers.lean.groundtruth.catalan_numbers_proof_auto
import Algorithms.catalan_numbers.lean.groundtruth.proof_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace Algorithms.catalan_numbers.lean.groundtruth.catalan_numbers_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.catalan_numbers.lean.groundtruth.catalan_numbers_goal
open Algorithms.catalan_numbers.lean
open Algorithms.catalan_numbers.lean.groundtruth.proof_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem sum_cell_int_range (n : Int) (table : List Int) (row col : Int)
    (hn : 0 ≤ n ∧ n ≤ 7) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : StackRowProgress n table row col) :
    INT_MIN ≤ Znth (StackCellIndex n (row - 1) (col + 1)) table 0 +
        Znth (StackCellIndex n row (col - 1)) table 0 ∧
    Znth (StackCellIndex n (row - 1) (col + 1)) table 0 +
        Znth (StackCellIndex n row (col - 1)) table 0 ≤ INT_MAX := by
  have hb := (StackRowProgress_add_step_extend__cell_dp n table row col hn hr hc hp).2.2
  have hl := hp.2.2.2.1.2
  rw [app_Znth2 0 table _ (StackCellIndex n row col) (by change Zlength table ≤ row * (n + 1) + col; omega), hl] at hb
  simp only [StackCellIndex, Int.sub_self] at hb
  exact StackCellBound_int_range__cell_dp row col _ (by omega) (by omega) hb

theorem proof_of_id_return_wit_1_split_goal_1 : id_return_wit_1_split_goal_1 := by
  unfold id_return_wit_1_split_goal_1
  intro y_pre x_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hm := Int.mul_le_mul_of_nonneg_right PreH4 (show 0 ≤ n_pre + 1 by omega)
  simp only [Int.add_mul, Int.one_mul]
  omega

theorem proof_of_id_return_wit_1 : id_return_wit_1 := by
  unfold id_return_wit_1
  right
  intro y_pre x_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_id_return_wit_1_split_goal_1 y_pre x_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_solve_safety_wit_10_split_goal_1 : solve_safety_wit_10_split_goal_1 := by
  unfold solve_safety_wit_10_split_goal_1
  intro f_pre n_pre table i j retval_3 retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  have h := (sum_cell_int_range n_pre table i j (by omega) (by omega) (by omega) PreH22).2
  simpa only [PreH1, PreH4, Int.sub_zero, StackCellIndex] using h

theorem proof_of_solve_safety_wit_10_split_goal_2 : solve_safety_wit_10_split_goal_2 := by
  unfold solve_safety_wit_10_split_goal_2
  intro f_pre n_pre table i j retval_3 retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  have h := (sum_cell_int_range n_pre table i j (by omega) (by omega) (by omega) PreH22).1
  simpa only [PreH1, PreH4, Int.sub_zero, StackCellIndex] using h

theorem proof_of_solve_safety_wit_10 : solve_safety_wit_10 := by
  unfold solve_safety_wit_10
  right
  intro f_pre n_pre table i j retval_3 retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pures
  all_goals first
    | exact proof_of_solve_safety_wit_10_split_goal_1 f_pre n_pre table i j retval_3 retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
    | exact proof_of_solve_safety_wit_10_split_goal_2 f_pre n_pre table i j retval_3 retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solve_entail_wit_1 : solve_entail_wit_1 := by
  unfold solve_entail_wit_1
  right
  intro f_pre n_pre PreH1 PreH2
  Exists ([] : List Int)
  simp only [Int.zero_mul]
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg f_pre ((n_pre + 1) * (n_pre + 1)))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.seg_empty f_pre 0 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (exact ⟨by omega, PreH1, ⟨by simp, by simp [Zlength]⟩,
          fun r c hr hc hi => by simp only [Int.zero_mul] at hi; omega⟩)
      | omega
      | rfl

theorem proof_of_solve_entail_wit_2 : solve_entail_wit_2 := by
  unfold solve_entail_wit_2
  right
  intro f_pre n_pre table_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hp : StackRowProgress n_pre table_2 i 0 :=
    ⟨PreH4, ⟨by omega, by omega⟩, by simpa only [Int.add_zero] using PreH6.2⟩
  Exists table_2
  simp only [Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_solve_entail_wit_3_split_goal_1 : solve_entail_wit_3_split_goal_1 := by
  unfold solve_entail_wit_3_split_goal_1
  intro n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simp only [Int.sub_mul, Int.one_mul]
  omega

theorem proof_of_solve_entail_wit_3_split_goal_2 : solve_entail_wit_3_split_goal_2 := by
  unfold solve_entail_wit_3_split_goal_2
  intro n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hm := Int.mul_le_mul_of_nonneg_right PreH7 (show 0 ≤ n_pre + 1 by omega)
  simp only [Int.add_mul, Int.one_mul]
  omega

theorem proof_of_solve_entail_wit_3 : solve_entail_wit_3 := by
  unfold solve_entail_wit_3
  right
  intro n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solve_entail_wit_3_split_goal_1 n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_solve_entail_wit_3_split_goal_2 n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1 := by
  unfold solve_entail_wit_4_split_goal_1
  intro n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simp only [Int.sub_mul, Int.one_mul]
  omega

theorem proof_of_solve_entail_wit_4_split_goal_2 : solve_entail_wit_4_split_goal_2 := by
  unfold solve_entail_wit_4_split_goal_2
  intro n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hm := Int.mul_le_mul_of_nonneg_right PreH7 (show 0 ≤ n_pre + 1 by omega)
  simp only [Int.add_mul, Int.one_mul]
  omega

theorem proof_of_solve_entail_wit_4 : solve_entail_wit_4 := by
  unfold solve_entail_wit_4
  right
  intro n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solve_entail_wit_4_split_goal_1 n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_solve_entail_wit_4_split_goal_2 n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solve_entail_wit_5_1_split_goal_1 : solve_entail_wit_5_1_split_goal_1 := by
  unfold solve_entail_wit_5_1_split_goal_1
  intro n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  subst i
  have h := (StackRowProgress_zero_row_extend__cell_dp n_pre table_2 j (by omega) (by omega) PreH12).1
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_1_split_goal_2 : solve_entail_wit_5_1_split_goal_2 := by
  unfold solve_entail_wit_5_1_split_goal_2
  intro n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  subst i
  have h := (StackRowProgress_zero_row_extend__cell_dp n_pre table_2 j (by omega) (by omega) PreH12).2.1
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_1_split_goal_3 : solve_entail_wit_5_1_split_goal_3 := by
  unfold solve_entail_wit_5_1_split_goal_3
  intro n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  subst i
  have h := (StackRowProgress_zero_row_extend__cell_dp n_pre table_2 j (by omega) (by omega) PreH12).2.2
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1 := by
  unfold solve_entail_wit_5_1
  right
  intro n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solve_entail_wit_5_1_split_goal_1 n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solve_entail_wit_5_1_split_goal_2 n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solve_entail_wit_5_1_split_goal_3 n_pre table_2 j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solve_entail_wit_5_2_split_goal_1 : solve_entail_wit_5_2_split_goal_1 := by
  unfold solve_entail_wit_5_2_split_goal_1
  intro n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst j
  have h := (StackRowProgress_copy_boundary_extend__cell_dp n_pre table_2 i (by omega) (by omega) PreH16).1
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_2_split_goal_2 : solve_entail_wit_5_2_split_goal_2 := by
  unfold solve_entail_wit_5_2_split_goal_2
  intro n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst j
  have h := (StackRowProgress_copy_boundary_extend__cell_dp n_pre table_2 i (by omega) (by omega) PreH16).2.1
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_2_split_goal_3 : solve_entail_wit_5_2_split_goal_3 := by
  unfold solve_entail_wit_5_2_split_goal_3
  intro n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst j
  have h := (StackRowProgress_copy_boundary_extend__cell_dp n_pre table_2 i (by omega) (by omega) PreH16).2.2
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2 := by
  unfold solve_entail_wit_5_2
  right
  intro n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solve_entail_wit_5_2_split_goal_1 n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_solve_entail_wit_5_2_split_goal_2 n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_solve_entail_wit_5_2_split_goal_3 n_pre table_2 i j retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solve_entail_wit_5_3_split_goal_1 : solve_entail_wit_5_3_split_goal_1 := by
  unfold solve_entail_wit_5_3_split_goal_1
  intro n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have h := (StackRowProgress_add_step_extend__cell_dp n_pre table_2 i j (by omega) (by omega) (by omega) PreH22).1
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_3_split_goal_2 : solve_entail_wit_5_3_split_goal_2 := by
  unfold solve_entail_wit_5_3_split_goal_2
  intro n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have h := (StackRowProgress_add_step_extend__cell_dp n_pre table_2 i j (by omega) (by omega) (by omega) PreH22).2.1
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_3_split_goal_3 : solve_entail_wit_5_3_split_goal_3 := by
  unfold solve_entail_wit_5_3_split_goal_3
  intro n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have h := (StackRowProgress_add_step_extend__cell_dp n_pre table_2 i j (by omega) (by omega) (by omega) PreH22).2.2
  simpa only [StackCellIndex, Int.sub_zero, Int.zero_mul, Int.add_zero, Int.zero_add] using h

theorem proof_of_solve_entail_wit_5_3 : solve_entail_wit_5_3 := by
  unfold solve_entail_wit_5_3
  right
  intro n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solve_entail_wit_5_3_split_goal_1 n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_solve_entail_wit_5_3_split_goal_2 n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_solve_entail_wit_5_3_split_goal_3 n_pre table_2 i j retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solve_entail_wit_6 : solve_entail_wit_6 := by
  unfold solve_entail_wit_6
  right
  intro f_pre n_pre table_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  Exists table_2
  simp only [Int.add_assoc]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_solve_entail_wit_7 : solve_entail_wit_7 := by
  unfold solve_entail_wit_7
  right
  intro f_pre n_pre table_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : j = n_pre + 1 := by omega
  subst j
  have hp : StackRowsDone n_pre table_2 (i + 1) :=
    ⟨by omega, by simpa only [Int.add_mul, Int.one_mul] using PreH8.2.2⟩
  Exists table_2
  simp only [Int.add_mul, Int.one_mul]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_solve_entail_wit_9 : solve_entail_wit_9 := by
  unfold solve_entail_wit_9
  right
  intro f_pre n_pre table_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have he : i = n_pre + 1 := by omega
  subst i
  have hm := Int.mul_nonneg PreH2 (show 0 ≤ n_pre + 1 by omega)
  have hlt : n_pre * (n_pre + 1) < (n_pre + 1) * (n_pre + 1) := by
    simp only [Int.add_mul, Int.one_mul]
    omega
  have hcorrect := (PreH6.2.2.2 n_pre 0 (by omega) (by omega) (by
    simpa only [StackCellIndex, Int.add_zero] using And.intro hm hlt)).2
  have hcount : StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table_2 0) := by
    apply StackCompletionCount_zero_to_StackSequenceCount
    simpa only [StackCellIndex, Int.add_zero] using hcorrect (by omega)
  Exists table_2
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty f_pre ((n_pre + 1) * (n_pre + 1)))).1)
  sep_apply (naive_C_Rules.IntArray.seg_to_full f_pre 0 ((n_pre + 1) * (n_pre + 1)) table_2)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_solve_return_wit_1_split_goal_1 : solve_return_wit_1_split_goal_1 := by
  unfold solve_return_wit_1_split_goal_1
  intro n_pre table_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  simpa only [Int.add_zero] using PreH9

theorem proof_of_solve_return_wit_1 : solve_return_wit_1 := by
  unfold solve_return_wit_1
  right
  intro n_pre table_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solve_return_wit_1_split_goal_1 n_pre table_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

end Algorithms.catalan_numbers.lean.groundtruth.catalan_numbers_proof_manual

