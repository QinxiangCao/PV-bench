import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_goal
import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_proof_auto
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open edit_strings_goal edit_strings_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
local macro "finish_entail" : tactic => `(tactic| (
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto))

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_1 : max_edit_string_matches_entail_wit_1_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_2 : max_edit_string_matches_entail_wit_1_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_3 : max_edit_string_matches_entail_wit_1_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_4 : max_edit_string_matches_entail_wit_1_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_5 : max_edit_string_matches_entail_wit_1_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine ⟨rfl, ?_⟩
  intro idx hi
  omega

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_6 : max_edit_string_matches_entail_wit_1_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine ⟨rfl, ?_⟩
  intro idx hi
  omega

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_7 : max_edit_string_matches_entail_wit_1_split_goal_7 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_7
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine ⟨rfl, ?_⟩
  intro idx hi
  omega

theorem proof_of_max_edit_string_matches_entail_wit_1_split_goal_8 : max_edit_string_matches_entail_wit_1_split_goal_8 := by
  unfold max_edit_string_matches_entail_wit_1_split_goal_8
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine ⟨rfl, ?_⟩
  intro idx hi
  omega

theorem proof_of_max_edit_string_matches_entail_wit_1 : max_edit_string_matches_entail_wit_1 := by
  unfold max_edit_string_matches_entail_wit_1
  right
  intro n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_1 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_2 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_3 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_4 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_5 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_6 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_7 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_1_split_goal_8 n_pre t2_l t1_l s2_l s1_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_1 : max_edit_string_matches_entail_wit_2_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_2 : max_edit_string_matches_entail_wit_2_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_3 : max_edit_string_matches_entail_wit_2_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_4 : max_edit_string_matches_entail_wit_2_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_5 : max_edit_string_matches_entail_wit_2_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply EditZeroPrefix_snoc_zero__zeroing_and_base_build
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_6 : max_edit_string_matches_entail_wit_2_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply EditZeroPrefix_snoc_zero__zeroing_and_base_build
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_7 : max_edit_string_matches_entail_wit_2_split_goal_7 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_7
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply EditZeroPrefix_snoc_zero__zeroing_and_base_build
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_2_split_goal_8 : max_edit_string_matches_entail_wit_2_split_goal_8 := by
  unfold max_edit_string_matches_entail_wit_2_split_goal_8
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply EditZeroPrefix_snoc_zero__zeroing_and_base_build
  assumption

theorem proof_of_max_edit_string_matches_entail_wit_2 : max_edit_string_matches_entail_wit_2 := by
  unfold max_edit_string_matches_entail_wit_2
  right
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_1 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_2 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_3 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_4 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_5 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_6 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_7 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_2_split_goal_8 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_3_split_goal_1 : max_edit_string_matches_entail_wit_3_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_3_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  first
    | exact PreH14
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_3_split_goal_2 : max_edit_string_matches_entail_wit_3_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_3_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  first
    | exact PreH14
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_3_split_goal_3 : max_edit_string_matches_entail_wit_3_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_3_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  first
    | exact PreH14
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_3_split_goal_4 : max_edit_string_matches_entail_wit_3_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_3_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  first
    | exact PreH14
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_3 : max_edit_string_matches_entail_wit_3 := by
  unfold max_edit_string_matches_entail_wit_3
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  Exists c21_2 c20_2 c11_2 c10_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_4 : max_edit_string_matches_entail_wit_4 := by
  unfold max_edit_string_matches_entail_wit_4
  right
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hi : i = n_pre := by omega
  subst i
  sep_apply (intArray.seg_to_full cnt10_pre 0 n_pre c10_2)
  sep_apply (intArray.seg_to_full cnt11_pre 0 n_pre c11_2)
  sep_apply (intArray.seg_to_full cnt20_pre 0 n_pre c20_2)
  sep_apply (intArray.seg_to_full cnt21_pre 0 n_pre c21_2)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  Exists c21_2 c20_2 c11_2 c10_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply EditZeroPrefix_to_full_at_bound__zeroing_and_base_build <;> first | assumption | omega)
      | (apply EditZeroFull_scratch_bound__zeroing_and_base_build
         all_goals first | omega | (apply EditZeroPrefix_to_full_at_bound__zeroing_and_base_build <;> first | assumption | omega))

theorem proof_of_max_edit_string_matches_entail_wit_5 : max_edit_string_matches_entail_wit_5 := by
  unfold max_edit_string_matches_entail_wit_5
  right
  intro seg1_pre n_pre t2_l t1_l s2_l s1_l c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  sep_apply (intArray.seg_single seg1_pre 0 (0 : Int))
  simp only [Int.zero_add]
  have hc0 := PreH11.2 0 (by omega)
  have hc1 := PreH12.2 0 (by omega)
  Exists ([0] : List Int)
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_1 : max_edit_string_matches_entail_wit_6_1_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_2 : max_edit_string_matches_entail_wit_6_1_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_3 : max_edit_string_matches_entail_wit_6_1_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_4 : max_edit_string_matches_entail_wit_6_1_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_5 : max_edit_string_matches_entail_wit_6_1_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply EditScratchCountsBound_replace_c10_zero_inc__zeroing_and_base_build
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_6 : max_edit_string_matches_entail_wit_6_1_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply EditBuildState_initial_s1_zero__zeroing_and_base_build
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_1 : max_edit_string_matches_entail_wit_6_1 := by
  unfold max_edit_string_matches_entail_wit_6_1
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_1 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_2 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_3 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_4 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_5 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_6 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_1 : max_edit_string_matches_entail_wit_6_2_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_2 : max_edit_string_matches_entail_wit_6_2_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_3 : max_edit_string_matches_entail_wit_6_2_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_4 : max_edit_string_matches_entail_wit_6_2_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  first
    | exact PreH20
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_5 : max_edit_string_matches_entail_wit_6_2_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply EditScratchCountsBound_replace_c11_zero_inc__zeroing_and_base_build
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_6 : max_edit_string_matches_entail_wit_6_2_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply EditBuildState_initial_s1_one__zeroing_and_base_build
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_2 : max_edit_string_matches_entail_wit_6_2 := by
  unfold max_edit_string_matches_entail_wit_6_2
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_1 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_2 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_3 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_4 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_5 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_6 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_7_split_goal_1 : max_edit_string_matches_entail_wit_7_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_7_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  first
    | exact PreH12
    | exact PreH13
    | exact PreH14
    | exact PreH15
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_7_split_goal_2 : max_edit_string_matches_entail_wit_7_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_7_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  first
    | exact PreH12
    | exact PreH13
    | exact PreH14
    | exact PreH15
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_7_split_goal_3 : max_edit_string_matches_entail_wit_7_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_7_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  first
    | exact PreH12
    | exact PreH13
    | exact PreH14
    | exact PreH15
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_7_split_goal_4 : max_edit_string_matches_entail_wit_7_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_7_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  first
    | exact PreH12
    | exact PreH13
    | exact PreH14
    | exact PreH15
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_7 : max_edit_string_matches_entail_wit_7 := by
  unfold max_edit_string_matches_entail_wit_7
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  Exists c21_2 c20_2 sg1_2 c10_2 c11_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_1 : max_edit_string_matches_entail_wit_8_1_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_2 : max_edit_string_matches_entail_wit_8_1_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_3 : max_edit_string_matches_entail_wit_8_1_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_4 : max_edit_string_matches_entail_wit_8_1_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_5 : max_edit_string_matches_entail_wit_8_1_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [(Znth (i-1) sg1_2 0)]) 0 = (Znth (i-1) sg1_2 0) := by
    rw [app_Znth2 (0 : Int) sg1_2 [(Znth (i-1) sg1_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t1_l i sg1_2 hs (by omega)
  have hc1 := PreH16.1.2 (Znth (i-1) sg1_2 0) (by omega)
  have hc2 := PreH16.2.1.2 (Znth (i-1) sg1_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_6 : max_edit_string_matches_entail_wit_8_1_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [(Znth (i-1) sg1_2 0)]) 0 = (Znth (i-1) sg1_2 0) := by
    rw [app_Znth2 (0 : Int) sg1_2 [(Znth (i-1) sg1_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t1_l i sg1_2 hs (by omega)
  have hc1 := PreH16.1.2 (Znth (i-1) sg1_2 0) (by omega)
  have hc2 := PreH16.2.1.2 (Znth (i-1) sg1_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_7 : max_edit_string_matches_entail_wit_8_1_split_goal_7 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_7
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [(Znth (i-1) sg1_2 0)]) 0 = (Znth (i-1) sg1_2 0) := by
    rw [app_Znth2 (0 : Int) sg1_2 [(Znth (i-1) sg1_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t1_l i sg1_2 hs (by omega)
  have hc1 := PreH16.1.2 (Znth (i-1) sg1_2 0) (by omega)
  have hc2 := PreH16.2.1.2 (Znth (i-1) sg1_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_8 : max_edit_string_matches_entail_wit_8_1_split_goal_8 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_8
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [(Znth (i-1) sg1_2 0)]) 0 = (Znth (i-1) sg1_2 0) := by
    rw [app_Znth2 (0 : Int) sg1_2 [(Znth (i-1) sg1_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t1_l i sg1_2 hs (by omega)
  have hc1 := PreH16.1.2 (Znth (i-1) sg1_2 0) (by omega)
  have hc2 := PreH16.2.1.2 (Znth (i-1) sg1_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_9 : max_edit_string_matches_entail_wit_8_1_split_goal_9 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_9
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [(Znth (i-1) sg1_2 0)]) 0 = (Znth (i-1) sg1_2 0) := by
    rw [app_Znth2 (0 : Int) sg1_2 [(Znth (i-1) sg1_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t1_l i sg1_2 hs (by omega)
  have hc1 := PreH16.1.2 (Znth (i-1) sg1_2 0) (by omega)
  have hc2 := PreH16.2.1.2 (Znth (i-1) sg1_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_10 : max_edit_string_matches_entail_wit_8_1_split_goal_10 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_10
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [(Znth (i-1) sg1_2 0)]) 0 = (Znth (i-1) sg1_2 0) := by
    rw [app_Znth2 (0 : Int) sg1_2 [(Znth (i-1) sg1_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t1_l i sg1_2 hs (by omega)
  have hc1 := PreH16.1.2 (Znth (i-1) sg1_2 0) (by omega)
  have hc2 := PreH16.2.1.2 (Znth (i-1) sg1_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_11 : max_edit_string_matches_entail_wit_8_1_split_goal_11 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_11
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH13.2.2.2.2

theorem proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_12 : max_edit_string_matches_entail_wit_8_1_split_goal_12 := by
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_12
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  try simp only [Int.sub_zero]
  apply EditSegmentPrefix_extend_open__build_s1_segments_counts
  all_goals first | assumption | omega | (unfold edit_edge_open; exact ⟨by assumption,by assumption⟩)

theorem proof_of_max_edit_string_matches_entail_wit_8_1 : max_edit_string_matches_entail_wit_8_1 := by
  unfold max_edit_string_matches_entail_wit_8_1
  right
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_1 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_2 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_3 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_4 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_5 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_6 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_7 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_8 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_9 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_10 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_11 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_12 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_1 : max_edit_string_matches_entail_wit_8_2_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  first
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_2 : max_edit_string_matches_entail_wit_8_2_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  first
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_3 : max_edit_string_matches_entail_wit_8_2_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  first
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_4 : max_edit_string_matches_entail_wit_8_2_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  first
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_5 : max_edit_string_matches_entail_wit_8_2_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH12.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH15.1.2 i (by omega)
  have hc2 := PreH15.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_6 : max_edit_string_matches_entail_wit_8_2_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH12.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH15.1.2 i (by omega)
  have hc2 := PreH15.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_7 : max_edit_string_matches_entail_wit_8_2_split_goal_7 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_7
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH12.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH15.1.2 i (by omega)
  have hc2 := PreH15.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_8 : max_edit_string_matches_entail_wit_8_2_split_goal_8 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_8
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH12.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH15.1.2 i (by omega)
  have hc2 := PreH15.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_9 : max_edit_string_matches_entail_wit_8_2_split_goal_9 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_9
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH12.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH15.1.2 i (by omega)
  have hc2 := PreH15.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_10 : max_edit_string_matches_entail_wit_8_2_split_goal_10 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_10
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH12.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH15.1.2 i (by omega)
  have hc2 := PreH15.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_11 : max_edit_string_matches_entail_wit_8_2_split_goal_11 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_11
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH12.2.2.2.2

theorem proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_12 : max_edit_string_matches_entail_wit_8_2_split_goal_12 := by
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_12
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH12.2.2.2.1
  try simp only [Int.sub_zero]
  apply EditSegmentPrefix_extend_new__build_s1_segments_counts
  all_goals first | assumption | omega | (unfold edit_edge_open; intro h; rcases h with ⟨h1,h2⟩; omega)

theorem proof_of_max_edit_string_matches_entail_wit_8_2 : max_edit_string_matches_entail_wit_8_2 := by
  unfold max_edit_string_matches_entail_wit_8_2
  right
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_1 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_2 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_3 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_4 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_5 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_6 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_7 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_8 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_9 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_10 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_11 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_12 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_1 : max_edit_string_matches_entail_wit_8_3_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_2 : max_edit_string_matches_entail_wit_8_3_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_3 : max_edit_string_matches_entail_wit_8_3_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_4 : max_edit_string_matches_entail_wit_8_3_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  first
    | exact PreH17
    | exact PreH18
    | exact PreH19
    | exact PreH20
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_5 : max_edit_string_matches_entail_wit_8_3_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH16.1.2 i (by omega)
  have hc2 := PreH16.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_6 : max_edit_string_matches_entail_wit_8_3_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH16.1.2 i (by omega)
  have hc2 := PreH16.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_7 : max_edit_string_matches_entail_wit_8_3_split_goal_7 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_7
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH16.1.2 i (by omega)
  have hc2 := PreH16.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_8 : max_edit_string_matches_entail_wit_8_3_split_goal_8 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_8
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH16.1.2 i (by omega)
  have hc2 := PreH16.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_9 : max_edit_string_matches_entail_wit_8_3_split_goal_9 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_9
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH16.1.2 i (by omega)
  have hc2 := PreH16.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_10 : max_edit_string_matches_entail_wit_8_3_split_goal_10 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_10
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg1_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg1_2 [i] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hc1 := PreH16.1.2 i (by omega)
  have hc2 := PreH16.2.1.2 i (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_11 : max_edit_string_matches_entail_wit_8_3_split_goal_11 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_11
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact PreH13.2.2.2.2

theorem proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_12 : max_edit_string_matches_entail_wit_8_3_split_goal_12 := by
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_12
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hs := PreH13.2.2.2.1
  try simp only [Int.sub_zero]
  apply EditSegmentPrefix_extend_new__build_s1_segments_counts
  all_goals first | assumption | omega | (unfold edit_edge_open; intro h; rcases h with ⟨h1,h2⟩; omega)

theorem proof_of_max_edit_string_matches_entail_wit_8_3 : max_edit_string_matches_entail_wit_8_3 := by
  unfold max_edit_string_matches_entail_wit_8_3
  right
  intro n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_1 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_2 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_3 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_4 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_5 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_6 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_7 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_8 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_9 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_10 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_11 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_12 n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_1 : max_edit_string_matches_entail_wit_9_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  first
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | exact PreH24
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_2 : max_edit_string_matches_entail_wit_9_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  first
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | exact PreH24
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_3 : max_edit_string_matches_entail_wit_9_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  first
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | exact PreH24
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_4 : max_edit_string_matches_entail_wit_9_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  first
    | exact PreH21
    | exact PreH22
    | exact PreH23
    | exact PreH24
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_5 : max_edit_string_matches_entail_wit_9_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [Int.sub_zero] at * <;> omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_6 : max_edit_string_matches_entail_wit_9_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [Int.sub_zero] at * <;> omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_7 : max_edit_string_matches_entail_wit_9_split_goal_7 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_7
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [Int.sub_zero] at * <;> omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_8 : max_edit_string_matches_entail_wit_9_split_goal_8 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_8
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [Int.sub_zero] at * <;> omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_9 : max_edit_string_matches_entail_wit_9_split_goal_9 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_9
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [Int.sub_zero] at * <;> omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_10 : max_edit_string_matches_entail_wit_9_split_goal_10 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_10
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [Int.sub_zero] at * <;> omega

theorem proof_of_max_edit_string_matches_entail_wit_9_split_goal_11 : max_edit_string_matches_entail_wit_9_split_goal_11 := by
  unfold max_edit_string_matches_entail_wit_9_split_goal_11
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  simp only [Int.sub_zero] at * <;> omega

theorem proof_of_max_edit_string_matches_entail_wit_9 : max_edit_string_matches_entail_wit_9 := by
  unfold max_edit_string_matches_entail_wit_9
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_1 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_2 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_3 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_4 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_5 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_6 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_7 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_8 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_9 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_10 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_9_split_goal_11 n_pre t2_l t1_l s2_l s1_l sg1 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_1 : max_edit_string_matches_entail_wit_10_1_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_2 : max_edit_string_matches_entail_wit_10_1_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_3 : max_edit_string_matches_entail_wit_10_1_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_4 : max_edit_string_matches_entail_wit_10_1_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_5 : max_edit_string_matches_entail_wit_10_1_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply (EditScratchCountsBound_inc_first__build_s1_segments_counts s1_l t1_l n_pre i c10_2 c11_2 c20_2 c21_2 block1)
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_6 : max_edit_string_matches_entail_wit_10_1_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply (EditBuildState_extend_zero__build_s1_segments_counts s1_l t1_l n_pre i sg1_2 c10_2 c11_2 block1)
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_1 : max_edit_string_matches_entail_wit_10_1 := by
  unfold max_edit_string_matches_entail_wit_10_1
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_1 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_2 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_3 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_4 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_5 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_6 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_1 : max_edit_string_matches_entail_wit_10_2_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_2 : max_edit_string_matches_entail_wit_10_2_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_3 : max_edit_string_matches_entail_wit_10_2_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_4 : max_edit_string_matches_entail_wit_10_2_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  first
    | exact PreH23
    | exact PreH24
    | exact PreH25
    | exact PreH26
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_5 : max_edit_string_matches_entail_wit_10_2_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply (EditScratchCountsBound_inc_second__build_s1_segments_counts s1_l t1_l n_pre i c10_2 c11_2 c20_2 c21_2 block1)
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_6 : max_edit_string_matches_entail_wit_10_2_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply (EditBuildState_extend_one__build_s1_segments_counts s1_l t1_l n_pre i sg1_2 c10_2 c11_2 block1)
  all_goals first | assumption | omega

theorem proof_of_max_edit_string_matches_entail_wit_10_2 : max_edit_string_matches_entail_wit_10_2 := by
  unfold max_edit_string_matches_entail_wit_10_2
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_1 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_2 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_3 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_4 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_5 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_6 n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_11_split_goal_1 : max_edit_string_matches_entail_wit_11_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_11_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_11_split_goal_2 : max_edit_string_matches_entail_wit_11_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_11_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_11_split_goal_3 : max_edit_string_matches_entail_wit_11_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_11_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_11_split_goal_4 : max_edit_string_matches_entail_wit_11_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_11_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  first
    | exact PreH15
    | exact PreH16
    | exact PreH17
    | exact PreH18
    | omega

theorem proof_of_max_edit_string_matches_entail_wit_11 : max_edit_string_matches_entail_wit_11 := by
  unfold max_edit_string_matches_entail_wit_11
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 block1 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  Exists c21_2 c20_2 sg1_2 c10_2 c11_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_12 : max_edit_string_matches_entail_wit_12 := by
  unfold max_edit_string_matches_entail_wit_12
  right
  intro seg1_pre n_pre t2_l t1_l s2_l s1_l c21_2 c20_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hi : i = n_pre := by omega
  subst i
  sep_apply (intArray.seg_to_full seg1_pre 0 n_pre sg1_2)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  Exists sg1_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_13 : max_edit_string_matches_entail_wit_13 := by
  unfold max_edit_string_matches_entail_wit_13
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  sep_apply (intArray.seg_single seg2_pre 0 (0 : Int))
  simp only [Int.zero_add]
  have hc0 := PreH9.2 0 (by omega)
  have hc1 := PreH10.2 0 (by omega)
  Exists c21_2 c20_2 sg1_2 c10_2 c11_2 ([0] : List Int)
  finish_entail

theorem EditScratchCountsBound_replace_c20_zero_inc__manual :
    ∀ n c10 c11 c20 c21,
      1 ≤ n → EditScratchCountsBound n c10 c11 c20 c21 → EditZeroFull n c20 →
      EditScratchCountsBound n c10 c11 (replace_Znth 0 (Znth 0 c20 0+1) c20) c21 := by
  intro n c10 c11 c20 c21 hn hs hz
  exact ⟨hs.1,hs.2.1,EditCountBounds_replace_zero_inc__zeroing_and_base_build n c20 hn hz,hs.2.2.2⟩
theorem EditScratchCountsBound_replace_c21_zero_inc__manual :
    ∀ n c10 c11 c20 c21,
      1 ≤ n → EditScratchCountsBound n c10 c11 c20 c21 → EditZeroFull n c21 →
      EditScratchCountsBound n c10 c11 c20 (replace_Znth 0 (Znth 0 c21 0+1) c21) := by
  intro n c10 c11 c20 c21 hn hs hz
  exact ⟨hs.1,hs.2.1,hs.2.2.1,EditCountBounds_replace_zero_inc__zeroing_and_base_build n c21 hn hz⟩

theorem proof_of_max_edit_string_matches_entail_wit_14_1 : max_edit_string_matches_entail_wit_14_1 := by
  unfold max_edit_string_matches_entail_wit_14_1
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (EditScratchCountsBound_replace_c20_zero_inc__manual) <;> first | assumption | omega | rfl)
      | (apply (EditBuildState_initial_s1_zero__zeroing_and_base_build) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_14_2 : max_edit_string_matches_entail_wit_14_2 := by
  unfold max_edit_string_matches_entail_wit_14_2
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (EditScratchCountsBound_replace_c21_zero_inc__manual) <;> first | assumption | omega | rfl)
      | (apply (EditBuildState_initial_s1_one__zeroing_and_base_build) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_15 : max_edit_string_matches_entail_wit_15 := by
  unfold max_edit_string_matches_entail_wit_15
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  Exists sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_1 : max_edit_string_matches_entail_wit_16_1_split_goal_1 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_1
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH19

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_2 : max_edit_string_matches_entail_wit_16_1_split_goal_2 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_2
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH18

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_3 : max_edit_string_matches_entail_wit_16_1_split_goal_3 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_3
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH17

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_4 : max_edit_string_matches_entail_wit_16_1_split_goal_4 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_4
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH16

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_5 : max_edit_string_matches_entail_wit_16_1_split_goal_5 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_5
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [(Znth (i-1) sg2_2 0)]) 0 = (Znth (i-1) sg2_2 0) := by
    rw [app_Znth2 (0 : Int) sg2_2 [(Znth (i-1) sg2_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t2_l i sg2_2 hs (by omega)
  have hc1 := PreH15.2.2.1.2 (Znth (i-1) sg2_2 0) (by omega)
  have hc2 := PreH15.2.2.2.2 (Znth (i-1) sg2_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_6 : max_edit_string_matches_entail_wit_16_1_split_goal_6 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_6
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [(Znth (i-1) sg2_2 0)]) 0 = (Znth (i-1) sg2_2 0) := by
    rw [app_Znth2 (0 : Int) sg2_2 [(Znth (i-1) sg2_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t2_l i sg2_2 hs (by omega)
  have hc1 := PreH15.2.2.1.2 (Znth (i-1) sg2_2 0) (by omega)
  have hc2 := PreH15.2.2.2.2 (Znth (i-1) sg2_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_7 : max_edit_string_matches_entail_wit_16_1_split_goal_7 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_7
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [(Znth (i-1) sg2_2 0)]) 0 = (Znth (i-1) sg2_2 0) := by
    rw [app_Znth2 (0 : Int) sg2_2 [(Znth (i-1) sg2_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t2_l i sg2_2 hs (by omega)
  have hc1 := PreH15.2.2.1.2 (Znth (i-1) sg2_2 0) (by omega)
  have hc2 := PreH15.2.2.2.2 (Znth (i-1) sg2_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_8 : max_edit_string_matches_entail_wit_16_1_split_goal_8 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_8
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [(Znth (i-1) sg2_2 0)]) 0 = (Znth (i-1) sg2_2 0) := by
    rw [app_Znth2 (0 : Int) sg2_2 [(Znth (i-1) sg2_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t2_l i sg2_2 hs (by omega)
  have hc1 := PreH15.2.2.1.2 (Znth (i-1) sg2_2 0) (by omega)
  have hc2 := PreH15.2.2.2.2 (Znth (i-1) sg2_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_9 : max_edit_string_matches_entail_wit_16_1_split_goal_9 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_9
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [(Znth (i-1) sg2_2 0)]) 0 = (Znth (i-1) sg2_2 0) := by
    rw [app_Znth2 (0 : Int) sg2_2 [(Znth (i-1) sg2_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t2_l i sg2_2 hs (by omega)
  have hc1 := PreH15.2.2.1.2 (Znth (i-1) sg2_2 0) (by omega)
  have hc2 := PreH15.2.2.2.2 (Znth (i-1) sg2_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_10 : max_edit_string_matches_entail_wit_16_1_split_goal_10 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_10
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [(Znth (i-1) sg2_2 0)]) 0 = (Znth (i-1) sg2_2 0) := by
    rw [app_Znth2 (0 : Int) sg2_2 [(Znth (i-1) sg2_2 0)] i (by omega), hlen]
    simp only [Int.sub_self]
    rfl
  try simp only [Int.sub_zero]
  rw [he]
  have hb := EditSegmentPrefix_last_block_bounds__build_s1_segments_counts t2_l i sg2_2 hs (by omega)
  have hc1 := PreH15.2.2.1.2 (Znth (i-1) sg2_2 0) (by omega)
  have hc2 := PreH15.2.2.2.2 (Znth (i-1) sg2_2 0) (by omega)
  omega

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_11 : max_edit_string_matches_entail_wit_16_1_split_goal_11 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_11
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH14.2.2.2.2

theorem proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_12 : max_edit_string_matches_entail_wit_16_1_split_goal_12 := by
  unfold max_edit_string_matches_entail_wit_16_1_split_goal_12
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  try simp only [Int.sub_zero]
  apply EditSegmentPrefix_extend_open__build_s1_segments_counts
  all_goals first | assumption | omega | (unfold edit_edge_open; exact ⟨by assumption,by assumption⟩)

theorem proof_of_max_edit_string_matches_entail_wit_16_1 : max_edit_string_matches_entail_wit_16_1 := by
  unfold max_edit_string_matches_entail_wit_16_1
  right
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  aggressive_pre_process
  all_goals first
    | (solve | dump_pre_spatial; intro idx_4 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_1 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx_4 ResultH))
    | (solve | dump_pre_spatial; intro idx_3 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_2 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx_3 ResultH))
    | (solve | dump_pre_spatial; intro idx_2 ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_3 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx_2 ResultH))
    | (solve | dump_pre_spatial; intro idx ResultH; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_4 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 idx ResultH))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_5 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_6 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_7 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_8 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_9 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_10 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_11 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | dump_pre_spatial; Goal_apply (proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_12 n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | trivial

theorem proof_of_max_edit_string_matches_entail_wit_16_2 : max_edit_string_matches_entail_wit_16_2 := by
  unfold max_edit_string_matches_entail_wit_16_2
  right
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := PreH13.2.2.2.1
  have hcounts := PreH13.2.2.2.2
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg2_2 [i] i (by omega),hlen]
    simp only [Int.sub_self]
    rfl
  have hc20 := PreH14.2.2.1.2 i (by omega)
  have hc21 := PreH14.2.2.2.2 i (by omega)
  have hseg : EditSegmentPrefix t2_l (i+1) (sg2_2 ++ [i]) := by
    apply EditSegmentPrefix_extend_new__build_s1_segments_counts
    all_goals first | assumption | omega | (unfold edit_edge_open; intro h; rcases h with ⟨h1,h2⟩; omega)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Int.sub_zero,he]
    all_goals first | assumption | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_16_3 : max_edit_string_matches_entail_wit_16_3 := by
  unfold max_edit_string_matches_entail_wit_16_3
  right
  intro n_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := PreH14.2.2.2.1
  have hcounts := PreH14.2.2.2.2
  have hlen := hs.1
  have he : Znth i (sg2_2 ++ [i]) 0 = i := by
    rw [app_Znth2 (0 : Int) sg2_2 [i] i (by omega),hlen]
    simp only [Int.sub_self]
    rfl
  have hc20 := PreH15.2.2.1.2 i (by omega)
  have hc21 := PreH15.2.2.2.2 i (by omega)
  have hseg : EditSegmentPrefix t2_l (i+1) (sg2_2 ++ [i]) := by
    apply EditSegmentPrefix_extend_new__build_s1_segments_counts
    all_goals first | assumption | omega | (unfold edit_edge_open; intro h; rcases h with ⟨h1,h2⟩; omega)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [Int.sub_zero,he]
    all_goals first | assumption | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_17 : max_edit_string_matches_entail_wit_17 := by
  unfold max_edit_string_matches_entail_wit_17
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2 c10_2 c11_2 c20_2 c21_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [Int.sub_zero] at *
  Exists c20_2 c21_2 sg1_2 c10_2 c11_2 sg2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_18_1 : max_edit_string_matches_entail_wit_18_1 := by
  unfold max_edit_string_matches_entail_wit_18_1
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 block2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_scratch_bound_update_zero__build_s2_segments_counts s2_l t2_l n_pre i sg2_2 c10_2 c11_2 c20_2 c21_2 block2) <;> first | assumption | omega | rfl)
      | (apply (EditBuildState_extend_zero__build_s1_segments_counts s2_l t2_l n_pre i sg2_2 c20_2 c21_2 block2) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_18_2 : max_edit_string_matches_entail_wit_18_2 := by
  unfold max_edit_string_matches_entail_wit_18_2
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 block2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH23 i (by omega)
  have hone : Znth i s2_l 0 = 1 := by omega
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_scratch_bound_update_one__build_s2_segments_counts s2_l t2_l n_pre i sg2_2 c10_2 c11_2 c20_2 c21_2 block2) <;> first | assumption | omega | rfl)
      | (apply (EditBuildState_extend_one__build_s1_segments_counts s2_l t2_l n_pre i sg2_2 c20_2 c21_2 block2) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_19 : max_edit_string_matches_entail_wit_19 := by
  unfold max_edit_string_matches_entail_wit_19
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 block2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  Exists sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_20 : max_edit_string_matches_entail_wit_20 := by
  unfold max_edit_string_matches_entail_wit_20
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hi : i = n_pre := by omega
  subst i
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.undef_seg_empty seg2_pre n_pre)).1)
  sep_apply (intArray.seg_to_full seg2_pre 0 n_pre sg2_2)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  Exists sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_21 : max_edit_string_matches_entail_wit_21 := by
  unfold max_edit_string_matches_entail_wit_21
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_greedy_prefix_state_start__greedy_common_and_mismatch_steps) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_22 : max_edit_string_matches_entail_wit_22 := by
  unfold max_edit_string_matches_entail_wit_22
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 ans PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_23 : max_edit_string_matches_entail_wit_23 := by
  unfold max_edit_string_matches_entail_wit_23
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1 sg2 c10_2 c11_2 c20_2 c21_2 ans i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hb := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1_l s2_l t1_l t2_l n_pre i ans sg1 sg2 c10_2 c11_2 c20_2 c21_2 PreH13 (by omega)
  rcases hb with ⟨hs1,hs2,hc10,hc11,hc20,hc21⟩
  have ha := edit_greedy_prefix_state_current_availability__greedy_common_and_mismatch_steps s1_l s2_l t1_l t2_l n_pre i ans sg1 sg2 c10_2 c11_2 c20_2 c21_2 PreH13 (by omega)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | (unfold EditGreedyCurrentAvailability; intro _; omega)

theorem proof_of_max_edit_string_matches_entail_wit_24 : max_edit_string_matches_entail_wit_24 := by
  unfold max_edit_string_matches_entail_wit_24
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_greedy_common_zero_step__greedy_common_and_mismatch_steps) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_25_1 : max_edit_string_matches_entail_wit_25_1 := by
  unfold max_edit_string_matches_entail_wit_25_1
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_greedy_common_one_step__greedy_common_and_mismatch_steps) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_25_2 : max_edit_string_matches_entail_wit_25_2 := by
  unfold max_edit_string_matches_entail_wit_25_2
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_greedy_common_one_step__greedy_common_and_mismatch_steps) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_27 : max_edit_string_matches_entail_wit_27 := by
  unfold max_edit_string_matches_entail_wit_27
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_greedy_s1_zero_s2_one_step__greedy_common_and_mismatch_steps) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_29 : max_edit_string_matches_entail_wit_29 := by
  unfold max_edit_string_matches_entail_wit_29
  right
  intro n_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (apply (edit_greedy_s1_one_s2_zero_step__greedy_common_and_mismatch_steps) <;> first | assumption | omega | rfl)

theorem proof_of_max_edit_string_matches_entail_wit_30_1 : max_edit_string_matches_entail_wit_30_1 := by
  unfold max_edit_string_matches_entail_wit_30_1
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hstate := PreH14
  obtain ⟨_,_,full10,full11,full20,full21,hbuild1,hbuild2,_⟩ := PreH14
  have hs1 := hbuild1.2.1
  have ht1 := hbuild1.2.2.1
  have hs2 := hbuild2.2.1
  have ht2 := hbuild2.2.2.1
  have hb (xs : List Int) (h : EditBinaryList xs n_pre) : ∀ idx, (0 ≤ idx ∧ idx < n_pre) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ 1 := by
    intro idx hi
    have hh := h.2 idx hi
    omega
  have hbs1 := hb s1_l hs1
  have hbs2 := hb s2_l hs2
  have hbt1 := hb t1_l ht1
  have hbt2 := hb t2_l ht2
  have hls1 := hs1.1
  have hls2 := hs2.1
  have hlt1 := ht1.1
  have hlt2 := ht2.1
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_30_2 : max_edit_string_matches_entail_wit_30_2 := by
  unfold max_edit_string_matches_entail_wit_30_2
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hstate := PreH14
  obtain ⟨_,_,full10,full11,full20,full21,hbuild1,hbuild2,_⟩ := PreH14
  have hs1 := hbuild1.2.1
  have ht1 := hbuild1.2.2.1
  have hs2 := hbuild2.2.1
  have ht2 := hbuild2.2.2.1
  have hb (xs : List Int) (h : EditBinaryList xs n_pre) : ∀ idx, (0 ≤ idx ∧ idx < n_pre) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ 1 := by
    intro idx hi
    have hh := h.2 idx hi
    omega
  have hbs1 := hb s1_l hs1
  have hbs2 := hb s2_l hs2
  have hbt1 := hb t1_l ht1
  have hbt2 := hb t2_l ht2
  have hls1 := hs1.1
  have hls2 := hs2.1
  have hlt1 := ht1.1
  have hlt2 := ht2.1
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_30_3 : max_edit_string_matches_entail_wit_30_3 := by
  unfold max_edit_string_matches_entail_wit_30_3
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hstate := PreH14
  obtain ⟨_,_,full10,full11,full20,full21,hbuild1,hbuild2,_⟩ := PreH14
  have hs1 := hbuild1.2.1
  have ht1 := hbuild1.2.2.1
  have hs2 := hbuild2.2.1
  have ht2 := hbuild2.2.2.1
  have hb (xs : List Int) (h : EditBinaryList xs n_pre) : ∀ idx, (0 ≤ idx ∧ idx < n_pre) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ 1 := by
    intro idx hi
    have hh := h.2 idx hi
    omega
  have hbs1 := hb s1_l hs1
  have hbs2 := hb s2_l hs2
  have hbt1 := hb t1_l ht1
  have hbt2 := hb t2_l ht2
  have hls1 := hs1.1
  have hls2 := hs2.1
  have hlt1 := ht1.1
  have hlt2 := ht2.1
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_30_4 : max_edit_string_matches_entail_wit_30_4 := by
  unfold max_edit_string_matches_entail_wit_30_4
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hstate := PreH14
  obtain ⟨_,_,full10,full11,full20,full21,hbuild1,hbuild2,_⟩ := PreH14
  have hs1 := hbuild1.2.1
  have ht1 := hbuild1.2.2.1
  have hs2 := hbuild2.2.1
  have ht2 := hbuild2.2.2.1
  have hb (xs : List Int) (h : EditBinaryList xs n_pre) : ∀ idx, (0 ≤ idx ∧ idx < n_pre) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ 1 := by
    intro idx hi
    have hh := h.2 idx hi
    omega
  have hbs1 := hb s1_l hs1
  have hbs2 := hb s2_l hs2
  have hbt1 := hb t1_l ht1
  have hbt2 := hb t2_l ht2
  have hls1 := hs1.1
  have hls2 := hs2.1
  have hlt1 := ht1.1
  have hlt2 := ht2.1
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_31 : max_edit_string_matches_entail_wit_31 := by
  unfold max_edit_string_matches_entail_wit_31
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 ans i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hi : i = n_pre := by omega
  subst i
  have hf := EditGreedyPrefixState_completed_state_facts s1_l s2_l t1_l t2_l n_pre ans sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH12 PreH13
  have hm := EditGreedyCompletedStateFacts_to_Maximum s1_l s2_l t1_l t2_l n_pre ans sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 hf
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2
  finish_entail

theorem proof_of_max_edit_string_matches_entail_wit_32 : max_edit_string_matches_entail_wit_32 := by
  unfold max_edit_string_matches_entail_wit_32
  left
  intro cnt21_pre cnt20_pre cnt11_pre cnt10_pre seg2_pre seg1_pre n_pre t2_pre t1_pre s2_pre s1_pre t2_l t1_l s2_l s1_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 ans PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hm := EditGreedyCompletedStateFacts_to_Maximum s1_l s2_l t1_l t2_l n_pre ans sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH7
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2
  finish_entail

end SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_proof_manual
