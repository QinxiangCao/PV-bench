import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_goal
import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open merging_stones_goal merging_stones_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev array2 := naive_C_Rules.IntArray2

private theorem merge_cell (addr n row col value : Int) (table : List (List Int)) (d : List Int)
    (hr : 0 ≤ row ∧ row < n) (hc : 0 ≤ col ∧ col < n) :
    (((addr+(row*n+col)*sizeof(INT)) # Int |-> value) **
      intArray.missing_i (addr+row*n*sizeof(INT)) col 0 n (Znth row table d) **
      array2.missing_i addr row 0 n n table) |--
    array2.full addr n n (replace_Znth row (replace_Znth col value (Znth row table d)) table) := by
  have he : addr+(row*n+col)*sizeof(INT) = addr+row*n*sizeof(INT)+col*sizeof(INT) := by ring
  rw [he]
  sep_apply (intArray.missing_i_merge_to_full (addr+row*n*sizeof(INT)) col n value (Znth row table d) hc)
  have ht : (intArray.full (addr+row*n*sizeof(INT)) n (replace_Znth col value (Znth row table d)) **
      array2.missing_i addr row 0 n n table |--
      array2.full addr n n (replace_Znth row (replace_Znth col value (Znth row table d)) table)) :=
    array2.missing_i_merge_to_full addr row n n table (replace_Znth col value (Znth row table d)) hr
  sep_apply ht
  cancel

private theorem restore_cell (addr n row col : Int) (table : List (List Int)) (d : List Int)
    (hr : 0 ≤ row ∧ row < n) (hc : 0 ≤ col ∧ col < n) :
    (((addr+(row*n+col)*sizeof(INT)) # Int |-> Znth col (Znth row table d) 0) **
      intArray.missing_i (addr+row*n*sizeof(INT)) col 0 n (Znth row table d) **
      array2.missing_i addr row 0 n n table) |-- array2.full addr n n table := by
  simpa only [replace_Znth_Znth] using merge_cell addr n row col
    (Znth col (Znth row table d) 0) table d hr hc

theorem proof_of_mergingStones_safety_wit_6_split_goal_1 : mergingStones_safety_wit_6_split_goal_1 := by
  unfold mergingStones_safety_wit_6_split_goal_1
  intro dp_pre prefix_pre n_pre stones_pre dp_init stones_l prefix_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  simp only [Int.sub_zero, INT_MAX, INT_MIN]
  omega

theorem proof_of_mergingStones_safety_wit_6_split_goal_2 : mergingStones_safety_wit_6_split_goal_2 := by
  unfold mergingStones_safety_wit_6_split_goal_2
  intro dp_pre prefix_pre n_pre stones_pre dp_init stones_l prefix_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  simp only [Int.sub_zero, INT_MAX, INT_MIN]
  omega

theorem proof_of_mergingStones_safety_wit_20_split_goal_1 : mergingStones_safety_wit_20_split_goal_1 := by
  unfold mergingStones_safety_wit_20_split_goal_1
  intro dp_pre prefix_pre n_pre stones_pre stones_l dp_l prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := StonePrefixDone_interval_bounds__prefix_math stones_l prefix_l n_pre left (left+len)
    PreH10 PreH11 ⟨by omega, by omega⟩ (by omega)
  dump_pre_spatial
  simp only [Int.sub_add_cancel, INT_MAX, INT_MIN]
  omega

theorem proof_of_mergingStones_safety_wit_20_split_goal_2 : mergingStones_safety_wit_20_split_goal_2 := by
  unfold mergingStones_safety_wit_20_split_goal_2
  intro dp_pre prefix_pre n_pre stones_pre stones_l dp_l prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := StonePrefixDone_interval_bounds__prefix_math stones_l prefix_l n_pre left (left+len)
    PreH10 PreH11 ⟨by omega, by omega⟩ (by omega)
  dump_pre_spatial
  simp only [Int.sub_add_cancel, INT_MAX, INT_MIN]
  omega

theorem proof_of_mergingStones_entail_wit_1_split_goal_1 : mergingStones_entail_wit_1_split_goal_1 := by
  unfold mergingStones_entail_wit_1_split_goal_1
  intro prefix_pre n_pre dp_init stones_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  dump_pre_spatial
  refine ⟨PreH5, rfl, ⟨by omega, by omega⟩, ?_⟩
  intro k hk
  have he : k = 0 := by omega
  subst k
  rfl

theorem proof_of_mergingStones_entail_wit_1_split_goal_spatial : mergingStones_entail_wit_1_split_goal_spatial := by
  unfold mergingStones_entail_wit_1_split_goal_spatial
  intro prefix_pre n_pre dp_init stones_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact intArray.seg_single prefix_pre 0 (0 : Int)

theorem proof_of_mergingStones_entail_wit_3_split_goal_1 : mergingStones_entail_wit_3_split_goal_1 := by
  unfold mergingStones_entail_wit_3_split_goal_1
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact (StoneMassesBounded_Znth__prefix_math _ _ _ PreH7 ⟨PreH5, PreH1⟩).2

theorem proof_of_mergingStones_entail_wit_3_split_goal_2 : mergingStones_entail_wit_3_split_goal_2 := by
  unfold mergingStones_entail_wit_3_split_goal_2
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact (StoneMassesBounded_Znth__prefix_math _ _ _ PreH7 ⟨PreH5, PreH1⟩).1

theorem proof_of_mergingStones_entail_wit_3_split_goal_3 : mergingStones_entail_wit_3_split_goal_3 := by
  unfold mergingStones_entail_wit_3_split_goal_3
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact (StonePrefixProgress_value_bounds__prefix_math _ _ _ _ _ PreH7 PreH3 PreH9 ⟨PreH5, le_refl _⟩).2

theorem proof_of_mergingStones_entail_wit_3_split_goal_4 : mergingStones_entail_wit_3_split_goal_4 := by
  unfold mergingStones_entail_wit_3_split_goal_4
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact (StonePrefixProgress_value_bounds__prefix_math _ _ _ _ _ PreH7 PreH3 PreH9 ⟨PreH5, le_refl _⟩).1

theorem proof_of_mergingStones_entail_wit_4_split_goal_1 : mergingStones_entail_wit_4_split_goal_1 := by
  unfold mergingStones_entail_wit_4_split_goal_1
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simp only [Int.sub_zero]
  exact StonePrefixProgress_extend__prefix_math _ _ _ _ PreH8 ⟨PreH3, PreH4⟩

theorem proof_of_mergingStones_entail_wit_5_split_goal_1 : mergingStones_entail_wit_5_split_goal_1 := by
  unfold mergingStones_entail_wit_5_split_goal_1
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have he : i = n_pre := by omega
  subst i
  exact PreH9

theorem proof_of_mergingStones_entail_wit_5_split_goal_2 : mergingStones_entail_wit_5_split_goal_2 := by
  unfold mergingStones_entail_wit_5_split_goal_2
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have := PreH9.2.1
  omega

theorem proof_of_mergingStones_entail_wit_6_split_goal_1 : mergingStones_entail_wit_6_split_goal_1 := by
  unfold mergingStones_entail_wit_6_split_goal_1
  intro n_pre dp_init stones_l prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact ⟨PreH7, ⟨by omega, by omega⟩, fun r c hr hc => False.elim (by omega)⟩

theorem proof_of_mergingStones_entail_wit_7_split_goal_1 : mergingStones_entail_wit_7_split_goal_1 := by
  unfold mergingStones_entail_wit_7_split_goal_1
  intro n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact ⟨PreH10.1, ⟨PreH6, PreH1⟩, ⟨by omega, by omega⟩, PreH10.2.2,
    fun c hc => False.elim (by omega)⟩

theorem proof_of_mergingStones_entail_wit_9_split_goal_1 : mergingStones_entail_wit_9_split_goal_1 := by
  unfold mergingStones_entail_wit_9_split_goal_1
  intro n_pre stones_l dp_l_2 col row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  refine ⟨PreH12.1, ⟨by omega, by omega⟩, ?_⟩
  intro r c hr hc
  by_cases hlt : r < row
  · exact PreH12.2.2.2.1 r c ⟨hr.1, hlt⟩ hc
  · have he : r = row := by omega
    subst r
    exact PreH12.2.2.2.2 c ⟨hc.1, by omega⟩

theorem proof_of_mergingStones_entail_wit_11_split_goal_1 : mergingStones_entail_wit_11_split_goal_1 := by
  unfold mergingStones_entail_wit_11_split_goal_1
  intro n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have he : row = n_pre := by omega
  subst row
  exact StoneLenDone_two_of_zero__zero_table _ _ _ PreH4 PreH2 PreH10

theorem proof_of_mergingStones_entail_wit_11_split_goal_2 : mergingStones_entail_wit_11_split_goal_2 := by
  unfold mergingStones_entail_wit_11_split_goal_2
  intro n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  convert PreH10 using 1 <;> omega

theorem proof_of_mergingStones_entail_wit_13_split_goal_1 : mergingStones_entail_wit_13_split_goal_1 := by
  unfold mergingStones_entail_wit_13_split_goal_1
  intro n_pre stones_l dp_l_2 prefix_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact StoneLenDone_to_initial_left_progress__table_progress _ _ _ _ PreH10 ⟨PreH4, PreH1⟩

theorem proof_of_mergingStones_entail_wit_14_split_goal_1 : mergingStones_entail_wit_14_split_goal_1 := by
  unfold mergingStones_entail_wit_14_split_goal_1
  intro n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact StoneSplitProgress_initial__prefix_math _ _ _ _ _ PreH12 PreH4

theorem proof_of_mergingStones_entail_wit_14_split_goal_2 : mergingStones_entail_wit_14_split_goal_2 := by
  unfold mergingStones_entail_wit_14_split_goal_2
  intro n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := StonePrefixDone_interval_bounds__prefix_math stones_l prefix_l n_pre left (left+len)
    PreH10 PreH11 ⟨by omega, by omega⟩ (by omega)
  simp only [Int.sub_add_cancel]
  omega

theorem proof_of_mergingStones_entail_wit_14_split_goal_3 : mergingStones_entail_wit_14_split_goal_3 := by
  unfold mergingStones_entail_wit_14_split_goal_3
  intro n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := StonePrefixDone_interval_bounds__prefix_math stones_l prefix_l n_pre left (left+len)
    PreH10 PreH11 ⟨by omega, by omega⟩ (by omega)
  simp only [Int.sub_add_cancel]
  omega

theorem proof_of_mergingStones_entail_wit_14_split_goal_4 : mergingStones_entail_wit_14_split_goal_4 := by
  unfold mergingStones_entail_wit_14_split_goal_4
  intro n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact StonePrefixDone_interval_sum__prefix_math _ _ _ _ _ PreH11 ⟨by omega, by omega⟩ (by omega)

theorem proof_of_mergingStones_entail_wit_16_split_goal_1 : mergingStones_entail_wit_16_split_goal_1 := by
  unfold mergingStones_entail_wit_16_split_goal_1
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hb := StoneSplitProgress_child_bounds__interval_min_core stones_l dp_l_2 n_pre len left split right best
    __default__List_Z PreH20 PreH3 PreH22 PreH8 ⟨by omega, by omega⟩ PreH10
  rw [←PreH8]
  exact hb.2.2

theorem proof_of_mergingStones_entail_wit_16_split_goal_2 : mergingStones_entail_wit_16_split_goal_2 := by
  unfold mergingStones_entail_wit_16_split_goal_2
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hb := StoneSplitProgress_child_bounds__interval_min_core stones_l dp_l_2 n_pre len left split right best
    __default__List_Z PreH20 PreH3 PreH22 PreH8 ⟨by omega, by omega⟩ PreH10
  rw [←PreH8]
  exact hb.2.1

theorem proof_of_mergingStones_entail_wit_16_split_goal_3 : mergingStones_entail_wit_16_split_goal_3 := by
  unfold mergingStones_entail_wit_16_split_goal_3
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hb := StoneSplitProgress_child_bounds__interval_min_core stones_l dp_l_2 n_pre len left split right best
    __default__List_Z PreH20 PreH3 PreH22 PreH8 ⟨by omega, by omega⟩ PreH10
  exact hb.1.2

theorem proof_of_mergingStones_entail_wit_16_split_goal_4 : mergingStones_entail_wit_16_split_goal_4 := by
  unfold mergingStones_entail_wit_16_split_goal_4
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hb := StoneSplitProgress_child_bounds__interval_min_core stones_l dp_l_2 n_pre len left split right best
    __default__List_Z PreH20 PreH3 PreH22 PreH8 ⟨by omega, by omega⟩ PreH10
  exact hb.1.1

theorem proof_of_mergingStones_entail_wit_19_1_split_goal_1 : mergingStones_entail_wit_19_1_split_goal_1 := by
  unfold mergingStones_entail_wit_19_1_split_goal_1
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  rw [←PreH15]
  exact StoneSplitProgress_replace_best__split_loop_step _ _ _ _ _ _ _ _ _ PreH8 PreH10 PreH16
    (by omega) PreH1 PreH18 PreH21

theorem proof_of_mergingStones_entail_wit_19_2_split_goal_1 : mergingStones_entail_wit_19_2_split_goal_1 := by
  unfold mergingStones_entail_wit_19_2_split_goal_1
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact StoneSplitProgress_keep_best__split_loop_step _ _ _ _ _ _ _ _ _ PreH8 PreH10 PreH17
    PreH1 PreH18 PreH21

theorem proof_of_mergingStones_entail_wit_19_2_split_goal_2 : mergingStones_entail_wit_19_2_split_goal_2 := by
  unfold mergingStones_entail_wit_19_2_split_goal_2
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21.2.2.1.1

theorem proof_of_mergingStones_entail_wit_20_split_goal_1 : mergingStones_entail_wit_20_split_goal_1 := by
  unfold mergingStones_entail_wit_20_split_goal_1
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH21.2.1

theorem proof_of_mergingStones_entail_wit_20_split_goal_2 : mergingStones_entail_wit_20_split_goal_2 := by
  unfold mergingStones_entail_wit_20_split_goal_2
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH20.1

theorem proof_of_mergingStones_entail_wit_20_split_goal_3 : mergingStones_entail_wit_20_split_goal_3 := by
  unfold mergingStones_entail_wit_20_split_goal_3
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [PreH13]
  exact (stone_interval_sum_bounds__arithmetic_safety _ _ _ _ PreH2 PreH5 (by omega) PreH10 PreH20).2

theorem proof_of_mergingStones_entail_wit_20_split_goal_4 : mergingStones_entail_wit_20_split_goal_4 := by
  unfold mergingStones_entail_wit_20_split_goal_4
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [PreH13]
  exact (stone_interval_sum_bounds__arithmetic_safety _ _ _ _ PreH2 PreH5 (by omega) PreH10 PreH20).1

theorem proof_of_mergingStones_entail_wit_21_split_goal_1 : mergingStones_entail_wit_21_split_goal_1 := by
  unfold mergingStones_entail_wit_21_split_goal_1
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he : split = right := by omega
  subst split
  rw [←PreH8]
  exact StoneSplitProgress_complete__interval_min_core _ _ _ _ _ _ _ PreH8 PreH9 PreH10 PreH22

theorem proof_of_mergingStones_entail_wit_21_split_goal_2 : mergingStones_entail_wit_21_split_goal_2 := by
  unfold mergingStones_entail_wit_21_split_goal_2
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  convert PreH22 using 1 <;> omega

theorem proof_of_mergingStones_entail_wit_21_split_goal_3 : mergingStones_entail_wit_21_split_goal_3 := by
  unfold mergingStones_entail_wit_21_split_goal_3
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he : split = right := by omega
  subst split
  have hm := StoneSplitProgress_complete__interval_min_core _ _ _ _ _ _ _ PreH8 PreH9 PreH10 PreH22
  exact (StoneIntervalMin_bounds__interval_min_core _ _ _ _ _ PreH20 PreH3 ⟨by omega, by omega⟩ PreH10 hm).2

theorem proof_of_mergingStones_entail_wit_23_split_goal_1 : mergingStones_entail_wit_23_split_goal_1 := by
  unfold mergingStones_entail_wit_23_split_goal_1
  intro n_pre stones_l prefix_l_2 dp_old dp_new len left right interval_sum best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH14.2.1

theorem proof_of_mergingStones_entail_wit_23_split_goal_2 : mergingStones_entail_wit_23_split_goal_2 := by
  unfold mergingStones_entail_wit_23_split_goal_2
  intro n_pre stones_l prefix_l_2 dp_old dp_new len left right interval_sum best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH13.1

theorem proof_of_mergingStones_entail_wit_24_split_goal_1 : mergingStones_entail_wit_24_split_goal_1 := by
  unfold mergingStones_entail_wit_24_split_goal_1
  intro n_pre stones_l dp_l_2 prefix_l_2 left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact StoneLeftProgress_to_next_len_done__table_progress _ _ _ _ _ PreH12 PreH1

theorem proof_of_mergingStones_entail_wit_25_split_goal_1 : mergingStones_entail_wit_25_split_goal_1 := by
  unfold mergingStones_entail_wit_25_split_goal_1
  intro n_pre stones_l prefix_l_2 dp_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact PreH6.2.1

theorem proof_of_mergingStones_entail_wit_25_split_goal_2 : mergingStones_entail_wit_25_split_goal_2 := by
  unfold mergingStones_entail_wit_25_split_goal_2
  intro n_pre stones_l prefix_l_2 dp_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact PreH5.1

theorem proof_of_mergingStones_entail_wit_26_split_goal_1 : mergingStones_entail_wit_26_split_goal_1 := by
  unfold mergingStones_entail_wit_26_split_goal_1
  intro n_pre stones_l dp_l_2 prefix_l_2 len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hf := StoneLenDone_final_facts__interval_min_core stones_l dp_l_2 n_pre len __default__List_Z
    PreH2 PreH3 PreH8 PreH1 PreH5 PreH10
  exact hf.2.2.2

theorem proof_of_mergingStones_entail_wit_26_split_goal_2 : mergingStones_entail_wit_26_split_goal_2 := by
  unfold mergingStones_entail_wit_26_split_goal_2
  intro n_pre stones_l dp_l_2 prefix_l_2 len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hf := StoneLenDone_final_facts__interval_min_core stones_l dp_l_2 n_pre len __default__List_Z
    PreH2 PreH3 PreH8 PreH1 PreH5 PreH10
  exact hf.2.2.1

theorem proof_of_mergingStones_entail_wit_26_split_goal_3 : mergingStones_entail_wit_26_split_goal_3 := by
  unfold mergingStones_entail_wit_26_split_goal_3
  intro n_pre stones_l dp_l_2 prefix_l_2 len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hf := StoneLenDone_final_facts__interval_min_core stones_l dp_l_2 n_pre len __default__List_Z
    PreH2 PreH3 PreH8 PreH1 PreH5 PreH10
  exact hf.2.1

theorem proof_of_mergingStones_entail_wit_26_split_goal_4 : mergingStones_entail_wit_26_split_goal_4 := by
  unfold mergingStones_entail_wit_26_split_goal_4
  intro n_pre stones_l dp_l_2 prefix_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  convert PreH10 using 1 <;> omega

theorem proof_of_mergingStones_safety_wit_6 : mergingStones_safety_wit_6 := by
  unfold mergingStones_safety_wit_6
  right
  intro dp_pre prefix_pre n_pre stones_pre dp_init stones_l prefix_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pures
  all_goals first
    | exact proof_of_mergingStones_safety_wit_6_split_goal_1 dp_pre prefix_pre n_pre stones_pre dp_init stones_l prefix_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_mergingStones_safety_wit_6_split_goal_2 dp_pre prefix_pre n_pre stones_pre dp_init stones_l prefix_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_mergingStones_safety_wit_20 : mergingStones_safety_wit_20 := by
  unfold mergingStones_safety_wit_20
  right
  intro dp_pre prefix_pre n_pre stones_pre stones_l dp_l prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pures
  all_goals first
    | exact proof_of_mergingStones_safety_wit_20_split_goal_1 dp_pre prefix_pre n_pre stones_pre stones_l dp_l prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_mergingStones_safety_wit_20_split_goal_2 dp_pre prefix_pre n_pre stones_pre stones_l dp_l prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_mergingStones_entail_wit_1 : mergingStones_entail_wit_1 := by
  unfold mergingStones_entail_wit_1
  right
  intro prefix_pre n_pre dp_init stones_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · exact intArray.seg_single prefix_pre 0 (0 : Int)
  · exact proof_of_mergingStones_entail_wit_1_split_goal_1 prefix_pre n_pre dp_init stones_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7

theorem proof_of_mergingStones_entail_wit_2 : mergingStones_entail_wit_2 := by
  unfold mergingStones_entail_wit_2
  right
  intro prefix_pre n_pre dp_init stones_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([0] : List Int) ?_
  split_pure_spatial
  · change (intArray.seg prefix_pre 0 1 [(0 : Int)] |-- intArray.seg prefix_pre 0 1 [(0 : Int)])
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3 := by
  unfold mergingStones_entail_wit_3
  right
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_3_split_goal_1 n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_mergingStones_entail_wit_3_split_goal_2 n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_mergingStones_entail_wit_3_split_goal_3 n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_mergingStones_entail_wit_3_split_goal_4 n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4 := by
  unfold mergingStones_entail_wit_4
  right
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_4_split_goal_1 n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5 := by
  unfold mergingStones_entail_wit_5
  right
  intro n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_5_split_goal_1 n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_mergingStones_entail_wit_5_split_goal_2 n_pre dp_init stones_l prefix_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6 := by
  unfold mergingStones_entail_wit_6
  right
  intro n_pre dp_init stones_l prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_6_split_goal_1 n_pre dp_init stones_l prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7

theorem proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7 := by
  unfold mergingStones_entail_wit_7
  right
  intro n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_7_split_goal_1 n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8 := by
  unfold mergingStones_entail_wit_8
  right
  intro dp_pre n_pre stones_l dp_l_2 col row prefix_l_2 __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  refine Automation.exp_right_rule (CRules := naive_C_Rules)
    (replace_Znth row (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z)) dp_l_2) ?_
  split_pure_spatial
  · exact merge_cell dp_pre n_pre row col 0 dp_l_2 __default__List_Z ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | exact StoneZeroProgress_store__zero_table _ _ _ _ _ PreH14 PreH3

theorem proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9 := by
  unfold mergingStones_entail_wit_9
  right
  intro n_pre stones_l dp_l_2 col row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_9_split_goal_1 n_pre stones_l dp_l_2 col row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11 := by
  unfold mergingStones_entail_wit_11
  right
  intro n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_11_split_goal_1 n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_mergingStones_entail_wit_11_split_goal_2 n_pre stones_l dp_l_2 row prefix_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_mergingStones_entail_wit_13 : mergingStones_entail_wit_13 := by
  unfold mergingStones_entail_wit_13
  right
  intro n_pre stones_l dp_l_2 prefix_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_13_split_goal_1 n_pre stones_l dp_l_2 prefix_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14 := by
  unfold mergingStones_entail_wit_14
  right
  intro n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_14_split_goal_1 n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_mergingStones_entail_wit_14_split_goal_2 n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_mergingStones_entail_wit_14_split_goal_3 n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_mergingStones_entail_wit_14_split_goal_4 n_pre stones_l dp_l_2 prefix_l left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16 := by
  unfold mergingStones_entail_wit_16
  right
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_16_split_goal_1 n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_16_split_goal_2 n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_16_split_goal_3 n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_16_split_goal_4 n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_mergingStones_entail_wit_17 : mergingStones_entail_wit_17 := by
  unfold mergingStones_entail_wit_17
  right
  intro dp_pre n_pre stones_l prefix_l_2 dp_l len left right split interval_sum best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l ?_
  split_pure_spatial
  · exact restore_cell dp_pre n_pre left split dp_l __default__List_Z ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_mergingStones_entail_wit_18 : mergingStones_entail_wit_18 := by
  unfold mergingStones_entail_wit_18
  right
  intro dp_pre n_pre stones_l prefix_l_2 dp_l len left right split left_value interval_sum best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hcan := StoneSplitProgress_candidate_facts__interval_min_core stones_l dp_l n_pre len left split right best interval_sum
    __default__List_Z PreH21 PreH4 PreH23 PreH9 ⟨by omega, by omega⟩ PreH12 PreH14
  dsimp at hcan
  rw [←PreH13] at hcan
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l ?_
  split_pure_spatial
  · exact restore_cell dp_pre n_pre (split+1) right dp_l __default__List_Z ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | exact hcan.1.1 | exact hcan.1.2 | exact hcan.2

theorem proof_of_mergingStones_entail_wit_19_1 : mergingStones_entail_wit_19_1 := by
  unfold mergingStones_entail_wit_19_1
  right
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_19_1_split_goal_1 n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_mergingStones_entail_wit_19_2 : mergingStones_entail_wit_19_2 := by
  unfold mergingStones_entail_wit_19_2
  right
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_19_2_split_goal_1 n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_mergingStones_entail_wit_19_2_split_goal_2 n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_mergingStones_entail_wit_20 : mergingStones_entail_wit_20 := by
  unfold mergingStones_entail_wit_20
  right
  intro n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_20_split_goal_1 n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_20_split_goal_2 n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_20_split_goal_3 n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_20_split_goal_4 n_pre stones_l prefix_l_2 dp_l_2 len left right split left_value right_value interval_sum candidate best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_mergingStones_entail_wit_21 : mergingStones_entail_wit_21 := by
  unfold mergingStones_entail_wit_21
  right
  intro n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_21_split_goal_1 n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_21_split_goal_2 n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_mergingStones_entail_wit_21_split_goal_3 n_pre stones_l dp_l_2 prefix_l_2 best interval_sum split right left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_mergingStones_entail_wit_22 : mergingStones_entail_wit_22 := by
  unfold mergingStones_entail_wit_22
  right
  intro dp_pre n_pre stones_l prefix_l_2 dp_l len left right interval_sum best __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  let dp_new := replace_Znth left (replace_Znth right best (Znth left dp_l __default__List_Z)) dp_l
  have hs := StoneSplitProgress_table_shape__interval_min_core _ _ _ _ _ _ _ PreH19
  have hli : 0 ≤ left ∧ left < Zlength dp_l := by rw [hs.1]; omega
  have hri : 0 ≤ right ∧ right < Zlength (Znth left dp_l []) := by rw [hs.2 left ⟨by omega, by omega⟩]; omega
  have hup : StoneUpdatedCell stones_l dp_l dp_new left right best := by
    refine ⟨hli, hri, ?_, PreH20⟩
    dsimp [dp_new]
    rw [Znth_indep dp_l left __default__List_Z [] hli]
  have hnext := StoneUpdatedCell_to_next_left_progress__table_progress _ _ _ _ _ _ _ _
    PreH19.1 PreH9 PreH8 hup
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_new ?_
  split_pure_spatial
  · exact merge_cell dp_pre n_pre left right best dp_l __default__List_Z ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_mergingStones_entail_wit_23 : mergingStones_entail_wit_23 := by
  unfold mergingStones_entail_wit_23
  right
  intro n_pre stones_l prefix_l_2 dp_old dp_new len left right interval_sum best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_23_split_goal_1 n_pre stones_l prefix_l_2 dp_old dp_new len left right interval_sum best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_mergingStones_entail_wit_23_split_goal_2 n_pre stones_l prefix_l_2 dp_old dp_new len left right interval_sum best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_mergingStones_entail_wit_24 : mergingStones_entail_wit_24 := by
  unfold mergingStones_entail_wit_24
  right
  intro n_pre stones_l dp_l_2 prefix_l_2 left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_24_split_goal_1 n_pre stones_l dp_l_2 prefix_l_2 left len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_mergingStones_entail_wit_25 : mergingStones_entail_wit_25 := by
  unfold mergingStones_entail_wit_25
  right
  intro n_pre stones_l prefix_l_2 dp_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_25_split_goal_1 n_pre stones_l prefix_l_2 dp_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
      | exact proof_of_mergingStones_entail_wit_25_split_goal_2 n_pre stones_l prefix_l_2 dp_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7

theorem proof_of_mergingStones_entail_wit_26 : mergingStones_entail_wit_26 := by
  unfold mergingStones_entail_wit_26
  right
  intro n_pre stones_l dp_l_2 prefix_l_2 len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_mergingStones_entail_wit_26_split_goal_1 n_pre stones_l dp_l_2 prefix_l_2 len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_mergingStones_entail_wit_26_split_goal_2 n_pre stones_l dp_l_2 prefix_l_2 len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_mergingStones_entail_wit_26_split_goal_3 n_pre stones_l dp_l_2 prefix_l_2 len __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_mergingStones_entail_wit_26_split_goal_4 n_pre stones_l dp_l_2 prefix_l_2 len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_mergingStones_return_wit_1 : mergingStones_return_wit_1 := by
  unfold mergingStones_return_wit_1
  right
  intro dp_pre n_pre stones_l prefix_l_2 dp_l_2 __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  split_pure_spatial
  · exact restore_cell dp_pre n_pre 0 (n_pre-1) dp_l_2 __default__List_Z ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

end SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_proof_manual
