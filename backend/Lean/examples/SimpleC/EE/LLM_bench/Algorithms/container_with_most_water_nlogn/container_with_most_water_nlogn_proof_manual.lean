import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_goal
import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open container_with_most_water_nlogn_goal container_with_most_water_nlogn_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  apply merge_prefix_init__merge_core <;> assumption

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hstate := PreH19
  have he : output = left_pre+(i-left_pre)+(j-middle_pre) := by omega
  rw [he] at hstate
  apply merge_prefix_take_left__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j (left_pre+(i-left_pre)+(j-middle_pre))
  all_goals first | assumption | omega | (right; omega) | (left; omega)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 : mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 : mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hstate := PreH19
  have he : output = left_pre+(i-left_pre)+(j-middle_pre) := by omega
  rw [he] at hstate
  apply merge_prefix_take_right__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j (left_pre+(i-left_pre)+(j-middle_pre))
  all_goals first | assumption | omega | (right; omega) | (left; omega)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 : mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 : mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hstate := PreH18
  have he : output = left_pre+(i-left_pre)+(j-middle_pre) := by omega
  rw [he] at hstate
  have hei : i = middle_pre := by omega
  rw [hei] at hstate ⊢
  apply merge_prefix_take_right__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre middle_pre j (left_pre+(middle_pre-left_pre)+(j-middle_pre))
  all_goals first | assumption | omega | (right; omega) | (left; omega)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 : mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 : mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 : mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 := by
  unfold mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hi : i = middle_pre := by omega
  have hj : j = right_pre := by omega
  have hout : output = right_pre := by omega
  have hs := PreH18
  rw [hi,hj,hout] at hs
  apply merge_prefix_finish__merge_core <;> first | assumption | omega

theorem proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 : sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 := by
  unfold sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 : sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 := by
  unfold sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 : sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 := by
  unfold sortHeightIndexRangeNLogN_return_wit_1_split_goal_1
  intro right_pre left_pre count_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine ⟨by omega,by omega,by omega,by omega,by omega,⟨rfl,rfl,fun _ _ _ => ⟨rfl,rfl⟩⟩,List.Perm.refl _,by omega,by omega,by omega,?_⟩
  intro p q hp hpq hq
  have he : p=q := by omega
  rw [he]

theorem proof_of_sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 : sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 := by
  unfold sortHeightIndexRangeNLogN_return_wit_2_split_goal_1
  intro right_pre left_pre count_pre work0_i work0_h buffer0_h buffer0_i k buffer_i_2 buffer_h_2 work_i1 work_h1 work_i_2 work_h_2 work_mid_i work_mid_h middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hks : k = right_pre := by omega
  have hc := PreH20
  rw [hks] at hc
  have hs := PreH17
  dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at hs
  apply sort_range_after_merge_copy__sort_copy work0_h work0_i work_mid_h work_mid_i work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 work_h1 work_i1 left_pre middle right_pre
  all_goals first | assumption | omega

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength workHeight_pre count_pre work_h)
  Intros_p hlen
  dump_pre_spatial
  exact hlen

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength workIndex_pre count_pre work_i)
  Intros_p hlen
  dump_pre_spatial
  exact hlen

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength bufferHeight_pre count_pre buffer_h)
  Intros_p hlen
  dump_pre_spatial
  exact hlen

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength bufferIndex_pre count_pre buffer_i)
  Intros_p hlen
  dump_pre_spatial
  exact hlen

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1 : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h work_mid_h work_mid_i work_h work_i buffer_h buffer_i middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  dump_pre_spatial
  omega

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2 : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2 := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h work_mid_h work_mid_i work_h work_i buffer_h buffer_i middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  dump_pre_spatial
  omega

theorem proof_of_maxAreaNLogN_safety_wit_8_split_goal_1 : maxAreaNLogN_safety_wit_8_split_goal_1 := by
  unfold maxAreaNLogN_safety_wit_8_split_goal_1
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hb := sorted_index_bounds__max_init l sorted_h sorted_i k PreH12 ⟨by omega,by omega⟩
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_maxAreaNLogN_safety_wit_8_split_goal_2 : maxAreaNLogN_safety_wit_8_split_goal_2 := by
  unfold maxAreaNLogN_safety_wit_8_split_goal_2
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hb := sorted_index_bounds__max_init l sorted_h sorted_i k PreH12 ⟨by omega,by omega⟩
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_maxAreaNLogN_safety_wit_9_split_goal_1 : maxAreaNLogN_safety_wit_9_split_goal_1 := by
  unfold maxAreaNLogN_safety_wit_9_split_goal_1
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hb := sorted_index_bounds__max_init l sorted_h sorted_i k PreH12 ⟨by omega,by omega⟩
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_maxAreaNLogN_safety_wit_9_split_goal_2 : maxAreaNLogN_safety_wit_9_split_goal_2 := by
  unfold maxAreaNLogN_safety_wit_9_split_goal_2
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hb := sorted_index_bounds__max_init l sorted_h sorted_i k PreH12 ⟨by omega,by omega⟩
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_maxAreaNLogN_entail_wit_1_split_goal_1 : maxAreaNLogN_entail_wit_1_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_1_split_goal_1
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  exact PreH4

theorem proof_of_maxAreaNLogN_entail_wit_1_split_goal_2 : maxAreaNLogN_entail_wit_1_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_1_split_goal_2
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  constructor <;> intro p hp <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_1_split_goal_3 : maxAreaNLogN_entail_wit_1_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_1_split_goal_3
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  constructor <;> intro p hp <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_1_split_goal_4 : maxAreaNLogN_entail_wit_1_split_goal_4 := by
  unfold maxAreaNLogN_entail_wit_1_split_goal_4
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_1_split_goal_5 : maxAreaNLogN_entail_wit_1_split_goal_5 := by
  unfold maxAreaNLogN_entail_wit_1_split_goal_5
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_1_split_goal_6 : maxAreaNLogN_entail_wit_1_split_goal_6 := by
  unfold maxAreaNLogN_entail_wit_1_split_goal_6
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_1_split_goal_7 : maxAreaNLogN_entail_wit_1_split_goal_7 := by
  unfold maxAreaNLogN_entail_wit_1_split_goal_7
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_2_split_goal_1 : maxAreaNLogN_entail_wit_2_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_2_split_goal_1
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact (workspace_prefix_snoc__max_init l buffer_h_2 buffer_i_2 k PreH9 PreH10 PreH12 ⟨by omega,by omega⟩).2.2

theorem proof_of_maxAreaNLogN_entail_wit_2_split_goal_2 : maxAreaNLogN_entail_wit_2_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_2_split_goal_2
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact (workspace_prefix_snoc__max_init l work_h_2 work_i_2 k PreH7 PreH8 PreH11 ⟨by omega,by omega⟩).2.2

theorem proof_of_maxAreaNLogN_entail_wit_2_split_goal_3 : maxAreaNLogN_entail_wit_2_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_2_split_goal_3
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_2_split_goal_4 : maxAreaNLogN_entail_wit_2_split_goal_4 := by
  unfold maxAreaNLogN_entail_wit_2_split_goal_4
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_2_split_goal_5 : maxAreaNLogN_entail_wit_2_split_goal_5 := by
  unfold maxAreaNLogN_entail_wit_2_split_goal_5
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_2_split_goal_6 : maxAreaNLogN_entail_wit_2_split_goal_6 := by
  unfold maxAreaNLogN_entail_wit_2_split_goal_6
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_4_split_goal_1 : maxAreaNLogN_entail_wit_4_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_4_split_goal_1
  intro heightSize_pre l work0_h work0_i buffer0_h buffer0_i work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH11

theorem proof_of_maxAreaNLogN_entail_wit_4_split_goal_2 : maxAreaNLogN_entail_wit_4_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_4_split_goal_2
  intro heightSize_pre l work0_h work0_i buffer0_h buffer0_i work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact full_sort_workspace__max_loop_setup l work0_h work0_i work_h work_i heightSize_pre PreH4 PreH5 PreH6 PreH9 PreH1

theorem proof_of_maxAreaNLogN_entail_wit_5_split_goal_1 : maxAreaNLogN_entail_wit_5_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_5_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5
  exact PreH5

theorem proof_of_maxAreaNLogN_entail_wit_5_split_goal_2 : maxAreaNLogN_entail_wit_5_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_5_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5
  apply processed_maximum_initial__max_loop_setup
  have he := PreH4.1.2.1
  omega

theorem proof_of_maxAreaNLogN_entail_wit_5_split_goal_3 : maxAreaNLogN_entail_wit_5_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_5_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5
  refine ⟨⟨0,⟨by omega,by omega⟩,rfl⟩,⟨0,⟨by omega,by omega⟩,rfl⟩,?_⟩
  intro p hp
  have he : p=0 := by omega
  rw [he]
  exact ⟨le_refl _,le_refl _⟩

theorem proof_of_maxAreaNLogN_entail_wit_5_split_goal_4 : maxAreaNLogN_entail_wit_5_split_goal_4 := by
  unfold maxAreaNLogN_entail_wit_5_split_goal_4
  intro heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h_2 sorted_i 0 PreH4 ⟨by omega,by omega⟩
  omega

theorem proof_of_maxAreaNLogN_entail_wit_5_split_goal_5 : maxAreaNLogN_entail_wit_5_split_goal_5 := by
  unfold maxAreaNLogN_entail_wit_5_split_goal_5
  intro heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h_2 sorted_i 0 PreH4 ⟨by omega,by omega⟩
  omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_1 : maxAreaNLogN_entail_wit_6_1_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_1
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact PreH18

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_2 : maxAreaNLogN_entail_wit_6_1_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_2
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  first | exact hb.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_3 : maxAreaNLogN_entail_wit_6_1_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_3
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  first | exact hb.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_4 : maxAreaNLogN_entail_wit_6_1_split_goal_4 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_4
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  first | exact hb.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_5 : maxAreaNLogN_entail_wit_6_1_split_goal_5 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_5
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hv := PreH18 (Znth k sorted_i 0) ⟨hb.1.1,by omega⟩
  rw [hb.2]
  first | exact hb.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_6 : maxAreaNLogN_entail_wit_6_1_split_goal_6 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_6
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hv := PreH18 (Znth k sorted_i 0) ⟨hb.1.1,by omega⟩
  rw [hb.2]
  first | exact hb.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_7 : maxAreaNLogN_entail_wit_6_1_split_goal_7 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_7
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  first | exact hb.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_8 : maxAreaNLogN_entail_wit_6_1_split_goal_8 := by
  unfold maxAreaNLogN_entail_wit_6_1_split_goal_8
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  first | exact hb.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_1 : maxAreaNLogN_entail_wit_9_1_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_1_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  exact PreH51

theorem proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_2 : maxAreaNLogN_entail_wit_9_1_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_1_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_a l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
    all_goals first | assumption | omega | (left; constructor <;> omega) | (right; constructor <;> omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_3 : maxAreaNLogN_entail_wit_9_1_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_1_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH49
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_1 : maxAreaNLogN_entail_wit_9_2_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_2_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  exact PreH51

theorem proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_2 : maxAreaNLogN_entail_wit_9_2_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_2_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_a l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
    all_goals first | assumption | omega | (left; constructor <;> omega) | (right; constructor <;> omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_3 : maxAreaNLogN_entail_wit_9_2_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_2_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH49
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_1 : maxAreaNLogN_entail_wit_9_3_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_3_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  exact PreH53

theorem proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_2 : maxAreaNLogN_entail_wit_9_3_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_3_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_a l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
    all_goals first | assumption | omega | (left; constructor <;> omega) | (right; constructor <;> omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_3 : maxAreaNLogN_entail_wit_9_3_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_3_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH51
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_1 : maxAreaNLogN_entail_wit_9_4_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_4_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  exact PreH53

theorem proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_2 : maxAreaNLogN_entail_wit_9_4_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_4_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_a l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
    all_goals first | assumption | omega | (left; constructor <;> omega) | (right; constructor <;> omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_3 : maxAreaNLogN_entail_wit_9_4_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_4_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH51
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_1 : maxAreaNLogN_entail_wit_9_5_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_5_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  exact PreH51

theorem proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_2 : maxAreaNLogN_entail_wit_9_5_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_5_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_a l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
    all_goals first | assumption | omega | (left; constructor <;> omega) | (right; constructor <;> omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_3 : maxAreaNLogN_entail_wit_9_5_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_5_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH49
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_1 : maxAreaNLogN_entail_wit_9_6_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_6_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  exact PreH51

theorem proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_2 : maxAreaNLogN_entail_wit_9_6_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_6_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_a l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
    all_goals first | assumption | omega | (left; constructor <;> omega) | (right; constructor <;> omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_3 : maxAreaNLogN_entail_wit_9_6_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_6_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH49
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_1 : maxAreaNLogN_entail_wit_9_7_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_7_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  exact PreH53

theorem proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_2 : maxAreaNLogN_entail_wit_9_7_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_7_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width
    all_goals try first | assumption | omega
    · intro x hx
      rw [abs_le]
      constructor <;> omega
    · first | (left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega) | (left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega) | (right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_3 : maxAreaNLogN_entail_wit_9_7_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_7_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH51
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_1 : maxAreaNLogN_entail_wit_9_8_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_8_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  exact PreH53

theorem proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_2 : maxAreaNLogN_entail_wit_9_8_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_8_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width
    all_goals try first | assumption | omega
    · intro x hx
      rw [abs_le]
      constructor <;> omega
    · first | (left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega) | (left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega) | (right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_3 : maxAreaNLogN_entail_wit_9_8_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_8_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH51
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_1 : maxAreaNLogN_entail_wit_9_9_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_9_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_2 : maxAreaNLogN_entail_wit_9_9_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_9_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width
    all_goals try first | assumption | omega
    · intro x hx
      rw [abs_le]
      constructor <;> omega
    · first | (left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega) | (left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega) | (right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_3 : maxAreaNLogN_entail_wit_9_9_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_9_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH33
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_1 : maxAreaNLogN_entail_wit_9_10_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_10_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_2 : maxAreaNLogN_entail_wit_9_10_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_10_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_3 : maxAreaNLogN_entail_wit_9_10_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_10_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_1 : maxAreaNLogN_entail_wit_9_11_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_11_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_2 : maxAreaNLogN_entail_wit_9_11_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_11_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width
    all_goals try first | assumption | omega
    · intro x hx
      rw [abs_le]
      constructor <;> omega
    · first | (left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega) | (left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega) | (right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_3 : maxAreaNLogN_entail_wit_9_11_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_11_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH33
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_1 : maxAreaNLogN_entail_wit_9_12_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_12_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_2 : maxAreaNLogN_entail_wit_9_12_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_12_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hx : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (max maximumArea (width*currentHeight)) := by
    apply processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width
    all_goals try first | assumption | omega
    · intro x hx
      rw [abs_le]
      constructor <;> omega
    · first | (left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega) | (left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega) | (right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega)
  convert hx using 1 <;> (simp only [max_def]; split <;> nlinarith)

theorem proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_3 : maxAreaNLogN_entail_wit_9_12_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_12_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hx := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) PreH33
  have hi : index = Znth k sorted_i_2 0 := by assumption
  rw [← hi] at hx
  convert hx using 1 <;> (simp only [min_def,max_def]; split <;> omega)

theorem proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_1 : maxAreaNLogN_entail_wit_9_13_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_13_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_2 : maxAreaNLogN_entail_wit_9_13_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_13_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_3 : maxAreaNLogN_entail_wit_9_13_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_13_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_1 : maxAreaNLogN_entail_wit_9_14_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_14_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_2 : maxAreaNLogN_entail_wit_9_14_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_14_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_3 : maxAreaNLogN_entail_wit_9_14_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_14_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_1 : maxAreaNLogN_entail_wit_9_15_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_15_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_2 : maxAreaNLogN_entail_wit_9_15_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_15_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_3 : maxAreaNLogN_entail_wit_9_15_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_15_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_1 : maxAreaNLogN_entail_wit_9_16_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_16_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_2 : maxAreaNLogN_entail_wit_9_16_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_16_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_3 : maxAreaNLogN_entail_wit_9_16_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_16_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_1 : maxAreaNLogN_entail_wit_9_17_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_17_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_2 : maxAreaNLogN_entail_wit_9_17_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_17_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_3 : maxAreaNLogN_entail_wit_9_17_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_17_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_1 : maxAreaNLogN_entail_wit_9_18_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_18_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_2 : maxAreaNLogN_entail_wit_9_18_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_18_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_3 : maxAreaNLogN_entail_wit_9_18_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_18_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hf := processed_endpoint_fresh__max_endpoint_c sorted_i_2 k minimumIndex maximumIndex index (by omega) (by rw [PreH32.1.2.1]; omega) (sorted_workspace_lookup__max_endpoint_c l sorted_h_2 sorted_i_2 PreH32) (by assumption) PreH33
  exfalso
  apply hf.1 <;> omega

theorem proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_1 : maxAreaNLogN_entail_wit_9_19_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_19_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_2 : maxAreaNLogN_entail_wit_9_19_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_19_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hlen := PreH32.1.2.1
  apply processed_max_extend__max_endpoint_d l sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
  all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_3 : maxAreaNLogN_entail_wit_9_19_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_19_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  apply processed_endpoints_extend__max_endpoint_d sorted_i_2 k index minimumIndex maximumIndex <;> first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_1 : maxAreaNLogN_entail_wit_9_20_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_20_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_2 : maxAreaNLogN_entail_wit_9_20_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_20_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hlen := PreH32.1.2.1
  apply processed_max_extend__max_endpoint_d l sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
  all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_3 : maxAreaNLogN_entail_wit_9_20_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_20_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  apply processed_endpoints_extend__max_endpoint_d sorted_i_2 k index minimumIndex maximumIndex <;> first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_1 : maxAreaNLogN_entail_wit_9_21_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_21_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_2 : maxAreaNLogN_entail_wit_9_21_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_21_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hlen := PreH32.1.2.1
  apply processed_max_extend__max_endpoint_d l sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
  all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_3 : maxAreaNLogN_entail_wit_9_21_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_21_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  apply processed_endpoints_extend__max_endpoint_d sorted_i_2 k index minimumIndex maximumIndex <;> first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_1 : maxAreaNLogN_entail_wit_9_22_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_22_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_2 : maxAreaNLogN_entail_wit_9_22_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_22_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hlen := PreH32.1.2.1
  apply processed_max_extend__max_endpoint_d l sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
  all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_3 : maxAreaNLogN_entail_wit_9_22_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_22_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  apply processed_endpoints_extend__max_endpoint_d sorted_i_2 k index minimumIndex maximumIndex <;> first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_1 : maxAreaNLogN_entail_wit_9_23_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_23_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_2 : maxAreaNLogN_entail_wit_9_23_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_23_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hlen := PreH32.1.2.1
  apply processed_max_extend__max_endpoint_d l sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
  all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_3 : maxAreaNLogN_entail_wit_9_23_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_23_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  apply processed_endpoints_extend__max_endpoint_d sorted_i_2 k index minimumIndex maximumIndex <;> first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_1 : maxAreaNLogN_entail_wit_9_24_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_9_24_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  exact PreH35

theorem proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_2 : maxAreaNLogN_entail_wit_9_24_split_goal_2 := by
  unfold maxAreaNLogN_entail_wit_9_24_split_goal_2
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hlen := PreH32.1.2.1
  apply processed_max_extend__max_endpoint_d l sorted_i_2 k index currentHeight minimumIndex maximumIndex width maximumArea
  all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_3 : maxAreaNLogN_entail_wit_9_24_split_goal_3 := by
  unfold maxAreaNLogN_entail_wit_9_24_split_goal_3
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  apply processed_endpoints_extend__max_endpoint_d sorted_i_2 k index minimumIndex maximumIndex <;> first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_10_split_goal_1 : maxAreaNLogN_entail_wit_10_split_goal_1 := by
  unfold maxAreaNLogN_entail_wit_10_split_goal_1
  intro heightSize_pre l sorted_h_2 sorted_i_2 maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  apply processed_full_prefix_maximum__max_final_result l sorted_h_2 sorted_i_2 maximumArea
  · omega
  · exact PreH12.1
  · have he : Zlength l = k := by omega
    rw [he]
    exact PreH14
  · intro p hp
    exact (PreH15 p ⟨hp.1,by omega⟩).1

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_1 : mergeHeightIndexRunsNLogN_entail_wit_1 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_1
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1 : mergeHeightIndexRunsNLogN_entail_wit_2_1 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_1
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2 : mergeHeightIndexRunsNLogN_entail_wit_2_2 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_2_2
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_4 : mergeHeightIndexRunsNLogN_entail_wit_4 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_4
  intro right_pre middle_pre left_pre count_pre destinationIndex_pre destinationHeight_pre sourceIndex_pre sourceHeight_pre dest0_i dest0_h source_i source_h output i j dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hnext : MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth output (Znth i source_h 0) dest_h_2) (replace_Znth output (Znth i source_i 0) dest_i_2) left_pre middle_pre right_pre (i+1) j (output+1) := by
    apply merge_prefix_take_left__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output
    all_goals first | assumption | omega | (left; exact PreH8)
  Right
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth output (Znth i source_i 0) dest_i_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth output (Znth i source_h 0) dest_h_2) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_6 : mergeHeightIndexRunsNLogN_entail_wit_6 := by
  unfold mergeHeightIndexRunsNLogN_entail_wit_6
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)

theorem proof_of_mergeHeightIndexRunsNLogN_return_wit_1 : mergeHeightIndexRunsNLogN_return_wit_1 := by
  unfold mergeHeightIndexRunsNLogN_return_wit_1
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)

theorem proof_of_sortHeightIndexRangeNLogN_safety_wit_3 : sortHeightIndexRangeNLogN_safety_wit_3 := by
  unfold sortHeightIndexRangeNLogN_safety_wit_3
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact (proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_sortHeightIndexRangeNLogN_entail_wit_1 : sortHeightIndexRangeNLogN_entail_wit_1 := by
  unfold sortHeightIndexRangeNLogN_entail_wit_1
  left
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h work_h_2 work_i_2 buffer_i_2 buffer_h_2 work_h_3 work_i_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  prop_apply (intArray.full_Zlength bufferHeight_pre count_pre buffer_h_2)
  Intros_p hbh
  prop_apply (intArray.full_Zlength bufferIndex_pre count_pre buffer_i_2)
  Intros_p hbi
  change Zlength buffer_h_2 = count_pre at hbh
  change Zlength buffer_i_2 = count_pre at hbi
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hd := range_sort_left_desc__sort_recursion work0_h work0_i work_h_2 work_i_2 work_h_3 work_i_3 left_pre (left_pre+Z.quot (right_pre-left_pre) 2) right_pre PreH2 PreH1
  have hr := PreH1.2.2.2.2.2.2.2
  have hs1 := PreH1
  have hs2 := PreH2
  dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at hs1 hs2
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_3 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_3 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | (rw [hq]; omega) | omega

theorem proof_of_sortHeightIndexRangeNLogN_entail_wit_2 : sortHeightIndexRangeNLogN_entail_wit_2 := by
  unfold sortHeightIndexRangeNLogN_entail_wit_2
  left
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 buffer_h_2 buffer_i_2 middle dest_h dest_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  prop_apply (intArray.full_Zlength bufferHeight_pre count_pre dest_h)
  Intros_p hdh
  prop_apply (intArray.full_Zlength bufferIndex_pre count_pre dest_i)
  Intros_p hdi
  change Zlength dest_h = count_pre at hdh
  change Zlength dest_i = count_pre at hdi
  have hm := PreH1
  dsimp only [HeightIndexRangeMergeResultNLogN,SameHeightIndexOutsideNLogN] at hm
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dest_i ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dest_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_h_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_sortHeightIndexRangeNLogN_entail_wit_3 : sortHeightIndexRangeNLogN_entail_wit_3 := by
  unfold sortHeightIndexRangeNLogN_entail_wit_3
  left
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 buffer0_h_2 buffer0_i_2 buffer_h_2 buffer_i_2 middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hc : CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h_2 work_i_2 left_pre right_pre left_pre := by
    constructor
    · intro p hp; omega
    · intro p hp hout; exact ⟨rfl,rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer0_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer0_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_h_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_sortHeightIndexRangeNLogN_entail_wit_4 : sortHeightIndexRangeNLogN_entail_wit_4 := by
  unfold sortHeightIndexRangeNLogN_entail_wit_4
  left
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h buffer0_h_2 buffer0_i_2 k buffer_i_2 buffer_h_2 work_i1_2 work_h1_2 work_i_2 work_h_2 work_mid_i_2 work_mid_h_2 middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hkh : 0 ≤ k ∧ k < Zlength work_h1_2 := ⟨by omega,by omega⟩
  have hki : 0 ≤ k ∧ k < Zlength work_i1_2 := ⟨by omega,by omega⟩
  have hc : CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 (replace_Znth k (Znth k buffer_h_2 0) work_h1_2) (replace_Znth k (Znth k buffer_i_2 0) work_i1_2) left_pre right_pre (k+1) := by
    constructor
    · intro p hp
      by_cases he : p=k
      · rw [he,Znth_replace_Znth_Same 0 work_h1_2 k _ hkh,Znth_replace_Znth_Same 0 work_i1_2 k _ hki]
        exact ⟨rfl,rfl⟩
      · rw [Znth_replace_Znth_Diff 0 work_h1_2 k p _ hkh ⟨by omega,by omega⟩ (Ne.symm he),Znth_replace_Znth_Diff 0 work_i1_2 k p _ hki ⟨by omega,by omega⟩ (Ne.symm he)]
        exact PreH20.1 p ⟨hp.1,by omega⟩
    · intro p hp hout
      have hne : k ≠ p := by rcases hout with h | h <;> omega
      rw [Znth_replace_Znth_Diff 0 work_h1_2 k p _ hkh ⟨hp.1,by omega⟩ hne,Znth_replace_Znth_Diff 0 work_i1_2 k p _ hki ⟨hp.1,by omega⟩ hne]
      apply PreH20.2 p hp
      rcases hout with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer0_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer0_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth k (Znth k buffer_i_2 0) work_i1_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth k (Znth k buffer_h_2 0) work_h1_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_h_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_sortHeightIndexRangeNLogN_return_wit_1 : sortHeightIndexRangeNLogN_return_wit_1 := by
  unfold sortHeightIndexRangeNLogN_return_wit_1
  right
  intro right_pre left_pre count_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 right_pre left_pre count_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_sortHeightIndexRangeNLogN_return_wit_2 : sortHeightIndexRangeNLogN_return_wit_2 := by
  unfold sortHeightIndexRangeNLogN_return_wit_2
  right
  intro right_pre left_pre count_pre work0_i work0_h buffer0_h buffer0_i k buffer_i_2 buffer_h_2 work_i1 work_h1 work_i_2 work_h_2 work_mid_i work_mid_h middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 right_pre left_pre count_pre work0_i work0_h buffer0_h buffer0_i k buffer_i_2 buffer_h_2 work_i1 work_h1 work_i_2 work_h_2 work_mid_i work_mid_h middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_1_pure
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_2_pure
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  all_goals first
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure := by
  unfold sortHeightIndexRangeNLogN_partial_solve_wit_3_pure
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h work_mid_h work_mid_i work_h work_i buffer_h buffer_i middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pures
  all_goals first
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h work_mid_h work_mid_i work_h work_i buffer_h buffer_i middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre work0_i work0_h work_mid_h work_mid_i work_h work_i buffer_h buffer_i middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxAreaNLogN_safety_wit_8 : maxAreaNLogN_safety_wit_8 := by
  unfold maxAreaNLogN_safety_wit_8
  right
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pures
  all_goals first
    | exact (proof_of_maxAreaNLogN_safety_wit_8_split_goal_1 bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | exact (proof_of_maxAreaNLogN_safety_wit_8_split_goal_2 bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

theorem proof_of_maxAreaNLogN_safety_wit_9 : maxAreaNLogN_safety_wit_9 := by
  unfold maxAreaNLogN_safety_wit_9
  right
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pures
  all_goals first
    | exact (proof_of_maxAreaNLogN_safety_wit_9_split_goal_1 bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | exact (proof_of_maxAreaNLogN_safety_wit_9_split_goal_2 bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

theorem proof_of_maxAreaNLogN_entail_wit_1 : maxAreaNLogN_entail_wit_1 := by
  unfold maxAreaNLogN_entail_wit_1
  right
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_1_split_goal_1 heightSize_pre l PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_maxAreaNLogN_entail_wit_1_split_goal_2 heightSize_pre l PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_maxAreaNLogN_entail_wit_1_split_goal_3 heightSize_pre l PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_maxAreaNLogN_entail_wit_1_split_goal_4 heightSize_pre l PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_maxAreaNLogN_entail_wit_1_split_goal_5 heightSize_pre l PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_maxAreaNLogN_entail_wit_1_split_goal_6 heightSize_pre l PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_maxAreaNLogN_entail_wit_1_split_goal_7 heightSize_pre l PreH1 PreH2 PreH3 PreH4)

theorem proof_of_maxAreaNLogN_entail_wit_2 : maxAreaNLogN_entail_wit_2 := by
  unfold maxAreaNLogN_entail_wit_2
  right
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_2_split_goal_1 heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | exact (proof_of_maxAreaNLogN_entail_wit_2_split_goal_2 heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | exact (proof_of_maxAreaNLogN_entail_wit_2_split_goal_3 heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | exact (proof_of_maxAreaNLogN_entail_wit_2_split_goal_4 heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | exact (proof_of_maxAreaNLogN_entail_wit_2_split_goal_5 heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | exact (proof_of_maxAreaNLogN_entail_wit_2_split_goal_6 heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)

theorem proof_of_maxAreaNLogN_entail_wit_3 : maxAreaNLogN_entail_wit_3 := by
  unfold maxAreaNLogN_entail_wit_3
  left
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i buffer_h work_i work_h k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hwork := workspace_prefix_complete__max_sort_boundary l work_h work_i k heightSize_pre PreH1 PreH6 PreH7 PreH8 PreH11
  have hbuffer := workspace_prefix_complete__max_sort_boundary l buffer_h buffer_i k heightSize_pre PreH1 PreH6 PreH9 PreH10 PreH12
  have hk : k = heightSize_pre := by omega
  rw [hk]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h ?_
  split_pure_spatial
  · sep_apply (intArray.undef_seg_empty bufferIndex_pre heightSize_pre)
    sep_apply (intArray.undef_seg_empty bufferHeight_pre heightSize_pre)
    sep_apply (intArray.undef_seg_empty workIndex_pre heightSize_pre)
    sep_apply (intArray.undef_seg_empty workHeight_pre heightSize_pre)
    cancel
    elim_emp
    try cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | exact hwork.2.2 | exact hbuffer.2.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_4 : maxAreaNLogN_entail_wit_4 := by
  unfold maxAreaNLogN_entail_wit_4
  right
  intro heightSize_pre l work0_h work0_i buffer0_h buffer0_i work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_4_split_goal_1 heightSize_pre l work0_h work0_i buffer0_h buffer0_i work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
      | exact (proof_of_maxAreaNLogN_entail_wit_4_split_goal_2 heightSize_pre l work0_h work0_i buffer0_h buffer0_i work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)

theorem proof_of_maxAreaNLogN_entail_wit_5 : maxAreaNLogN_entail_wit_5 := by
  unfold maxAreaNLogN_entail_wit_5
  right
  intro heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_5_split_goal_1 heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_maxAreaNLogN_entail_wit_5_split_goal_2 heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_maxAreaNLogN_entail_wit_5_split_goal_3 heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_maxAreaNLogN_entail_wit_5_split_goal_4 heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_maxAreaNLogN_entail_wit_5_split_goal_5 heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5)

theorem proof_of_maxAreaNLogN_entail_wit_6_1 : maxAreaNLogN_entail_wit_6_1 := by
  unfold maxAreaNLogN_entail_wit_6_1
  right
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_1 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_2 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_3 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_4 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_5 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_6 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_7 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_8 heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)

theorem proof_of_maxAreaNLogN_entail_wit_6_2 : maxAreaNLogN_entail_wit_6_2 := by
  unfold maxAreaNLogN_entail_wit_6_2
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hl := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hb : 0 ≤ minimumIndex ∧ minimumIndex ≤ maximumIndex ∧ maximumIndex < heightSize_pre := by
    apply processed_endpoint_bounds__max_width_selection sorted_i k minimumIndex maximumIndex heightSize_pre PreH16
    intro p hp
    have hh := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i p PreH15 ⟨hp.1,by omega⟩
    omega
  have hh := PreH18 (Znth k sorted_i 0) ⟨hl.1.1,by omega⟩
  have hh' : 0 ≤ Znth k sorted_h 0 ∧ Znth k sorted_h 0 ≤ 10000 := hl.2 ▸ hh
  Right
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_6_3 : maxAreaNLogN_entail_wit_6_3 := by
  unfold maxAreaNLogN_entail_wit_6_3
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hl := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hb : 0 ≤ minimumIndex ∧ minimumIndex ≤ maximumIndex ∧ maximumIndex < heightSize_pre := by
    apply processed_endpoint_bounds__max_width_selection sorted_i k minimumIndex maximumIndex heightSize_pre PreH16
    intro p hp
    have hh := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i p PreH15 ⟨hp.1,by omega⟩
    omega
  have hh := PreH18 (Znth k sorted_i 0) ⟨hl.1.1,by omega⟩
  have hh' : 0 ≤ Znth k sorted_h 0 ∧ Znth k sorted_h 0 ≤ 10000 := hl.2 ▸ hh
  Right
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_6_4 : maxAreaNLogN_entail_wit_6_4 := by
  unfold maxAreaNLogN_entail_wit_6_4
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hl := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hb : 0 ≤ minimumIndex ∧ minimumIndex ≤ maximumIndex ∧ maximumIndex < heightSize_pre := by
    apply processed_endpoint_bounds__max_width_selection sorted_i k minimumIndex maximumIndex heightSize_pre PreH16
    intro p hp
    have hh := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i p PreH15 ⟨hp.1,by omega⟩
    omega
  have hh := PreH18 (Znth k sorted_i 0) ⟨hl.1.1,by omega⟩
  have hh' : 0 ≤ Znth k sorted_h 0 ∧ Znth k sorted_h 0 ≤ 10000 := hl.2 ▸ hh
  Right
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_6_5 : maxAreaNLogN_entail_wit_6_5 := by
  unfold maxAreaNLogN_entail_wit_6_5
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hl := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hb : 0 ≤ minimumIndex ∧ minimumIndex ≤ maximumIndex ∧ maximumIndex < heightSize_pre := by
    apply processed_endpoint_bounds__max_width_selection sorted_i k minimumIndex maximumIndex heightSize_pre PreH16
    intro p hp
    have hh := sorted_workspace_lookup__max_width_selection l sorted_h sorted_i p PreH15 ⟨hp.1,by omega⟩
    omega
  have hh := PreH18 (Znth k sorted_i 0) ⟨hl.1.1,by omega⟩
  have hh' : 0 ≤ Znth k sorted_h 0 ∧ Znth k sorted_h 0 ≤ 10000 := hl.2 ▸ hh
  Right
  Right
  Right
  Left
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_7_1 : maxAreaNLogN_entail_wit_7_1 := by
  unfold maxAreaNLogN_entail_wit_7_1
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hd : distanceToMaximum = width := by omega
  rw [hd]
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_7_2 : maxAreaNLogN_entail_wit_7_2 := by
  unfold maxAreaNLogN_entail_wit_7_2
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hd : width_2 = distanceToMaximum_2 := by omega
  rw [hd]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_7_3 : maxAreaNLogN_entail_wit_7_3 := by
  unfold maxAreaNLogN_entail_wit_7_3
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hd : distanceToMaximum = width := by omega
  rw [hd]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_7_4 : maxAreaNLogN_entail_wit_7_4 := by
  unfold maxAreaNLogN_entail_wit_7_4
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hd : width_2 = distanceToMaximum_2 := by omega
  rw [hd]
  Right
  Right
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_1 : maxAreaNLogN_entail_wit_8_1 := by
  unfold maxAreaNLogN_entail_wit_8_1
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hd : width = distanceToMinimum := by omega
  rw [hd]
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_2 : maxAreaNLogN_entail_wit_8_2 := by
  unfold maxAreaNLogN_entail_wit_8_2
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hd : distanceToMinimum_2 = distanceToMaximum_2 := by omega
  have hw : width_2 = distanceToMaximum_2 := by omega
  rw [hd,hw]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_3 : maxAreaNLogN_entail_wit_8_3 := by
  unfold maxAreaNLogN_entail_wit_8_3
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hd : width = distanceToMinimum := by omega
  rw [hd]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_4 : maxAreaNLogN_entail_wit_8_4 := by
  unfold maxAreaNLogN_entail_wit_8_4
  intro bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hd : distanceToMinimum_2 = distanceToMaximum_2 := by omega
  have hw : width_2 = distanceToMaximum_2 := by omega
  rw [hd,hw]
  Right
  Right
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_9_1 : maxAreaNLogN_entail_wit_9_1 := by
  unfold maxAreaNLogN_entail_wit_9_1
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)

theorem proof_of_maxAreaNLogN_entail_wit_9_2 : maxAreaNLogN_entail_wit_9_2 := by
  unfold maxAreaNLogN_entail_wit_9_2
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)

theorem proof_of_maxAreaNLogN_entail_wit_9_3 : maxAreaNLogN_entail_wit_9_3 := by
  unfold maxAreaNLogN_entail_wit_9_3
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)

theorem proof_of_maxAreaNLogN_entail_wit_9_4 : maxAreaNLogN_entail_wit_9_4 := by
  unfold maxAreaNLogN_entail_wit_9_4
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)

theorem proof_of_maxAreaNLogN_entail_wit_9_5 : maxAreaNLogN_entail_wit_9_5 := by
  unfold maxAreaNLogN_entail_wit_9_5
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)

theorem proof_of_maxAreaNLogN_entail_wit_9_6 : maxAreaNLogN_entail_wit_9_6 := by
  unfold maxAreaNLogN_entail_wit_9_6
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)

theorem proof_of_maxAreaNLogN_entail_wit_9_7 : maxAreaNLogN_entail_wit_9_7 := by
  unfold maxAreaNLogN_entail_wit_9_7
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)

theorem proof_of_maxAreaNLogN_entail_wit_9_8 : maxAreaNLogN_entail_wit_9_8 := by
  unfold maxAreaNLogN_entail_wit_9_8
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53)

theorem proof_of_maxAreaNLogN_entail_wit_9_9 : maxAreaNLogN_entail_wit_9_9 := by
  unfold maxAreaNLogN_entail_wit_9_9
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_10 : maxAreaNLogN_entail_wit_9_10 := by
  unfold maxAreaNLogN_entail_wit_9_10
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_11 : maxAreaNLogN_entail_wit_9_11 := by
  unfold maxAreaNLogN_entail_wit_9_11
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_12 : maxAreaNLogN_entail_wit_9_12 := by
  unfold maxAreaNLogN_entail_wit_9_12
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_13 : maxAreaNLogN_entail_wit_9_13 := by
  unfold maxAreaNLogN_entail_wit_9_13
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_14 : maxAreaNLogN_entail_wit_9_14 := by
  unfold maxAreaNLogN_entail_wit_9_14
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_15 : maxAreaNLogN_entail_wit_9_15 := by
  unfold maxAreaNLogN_entail_wit_9_15
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_16 : maxAreaNLogN_entail_wit_9_16 := by
  unfold maxAreaNLogN_entail_wit_9_16
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_17 : maxAreaNLogN_entail_wit_9_17 := by
  unfold maxAreaNLogN_entail_wit_9_17
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_18 : maxAreaNLogN_entail_wit_9_18 := by
  unfold maxAreaNLogN_entail_wit_9_18
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_19 : maxAreaNLogN_entail_wit_9_19 := by
  unfold maxAreaNLogN_entail_wit_9_19
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_20 : maxAreaNLogN_entail_wit_9_20 := by
  unfold maxAreaNLogN_entail_wit_9_20
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_21 : maxAreaNLogN_entail_wit_9_21 := by
  unfold maxAreaNLogN_entail_wit_9_21
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_22 : maxAreaNLogN_entail_wit_9_22 := by
  unfold maxAreaNLogN_entail_wit_9_22
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_23 : maxAreaNLogN_entail_wit_9_23 := by
  unfold maxAreaNLogN_entail_wit_9_23
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_9_24 : maxAreaNLogN_entail_wit_9_24 := by
  unfold maxAreaNLogN_entail_wit_9_24
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_2 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
      | exact (proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_3 heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)

theorem proof_of_maxAreaNLogN_entail_wit_10 : maxAreaNLogN_entail_wit_10 := by
  unfold maxAreaNLogN_entail_wit_10
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_maxAreaNLogN_entail_wit_10_split_goal_1 heightSize_pre l sorted_h_2 sorted_i_2 maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_proof_manual
