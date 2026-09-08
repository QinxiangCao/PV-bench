import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_goal
import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open huffman_encoding_goal huffman_encoding_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1 := by
  unfold huffman_cost_entail_wit_1
  right
  intro n_pre weights_l PreH1 PreH2 PreH3 PreH4
  refine Automation.exp_right_rule (CRules := naive_C_Rules) weights_l ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | omega

theorem proof_of_huffman_cost_entail_wit_2 : huffman_cost_entail_wit_2 := by
  unfold huffman_cost_entail_wit_2
  right
  intro n_pre weights_l i copied_2 remaining_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  cases remaining_2 with
  | nil =>
    simp only [List.append_nil] at PreH6
    rw [PreH6] at PreH4
    omega
  | cons next tail =>
    have he : Znth (Zlength copied_2) (copied_2++next::tail) 0 = next := by
      rw [app_Znth2 0 copied_2 (next::tail) _ (le_refl _)]
      simp only [Int.sub_self, Znth0_cons]
    refine Automation.exp_right_rule (CRules := naive_C_Rules) tail ?_
    rw [he]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first
        | simp only [List.append_assoc, List.cons_append, List.nil_append]
        | rw [Zlength_app, Zlength_cons, Zlength_nil]; omega
        | rw [← PreH6]; omega
        | omega

theorem proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3 := by
  unfold huffman_cost_entail_wit_3
  right
  intro work_pre n_pre weights_l i copied remaining PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hei : i = n_pre := by omega
  have hr : remaining = [] := by
    have hh := congrArg Zlength PreH6
    rw [Zlength_app] at hh
    have hz : Zlength remaining = 0 := by omega
    cases remaining with
    | nil => rfl
    | cons a l => rw [Zlength_cons] at hz; have := Zlength_nonneg l; omega
  rw [hr, List.append_nil] at PreH6
  rw [← PreH6, hei]
  have hb := huffman_input_live_bounds__copy_initialization weights_l n_pre PreH4 PreH5
  have hp : HuffmanProgress weights_l weights_l n_pre 0 := by
    rw [← PreH4]; exact huffman_initial_progress__copy_initialization weights_l (by omega) PreH5
  refine Automation.exp_right_rule (CRules := naive_C_Rules) weights_l ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full work_pre 0 n_pre weights_l
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_huffman_cost_entail_wit_4_split_goal_1 : huffman_cost_entail_wit_4_split_goal_1 := by
  unfold huffman_cost_entail_wit_4_split_goal_1
  intro n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact huffman_min_scan_init__min_scan_updates work_l_2

theorem proof_of_huffman_cost_entail_wit_4_split_goal_2 : huffman_cost_entail_wit_4_split_goal_2 := by
  unfold huffman_cost_entail_wit_4_split_goal_2
  intro n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH11

theorem proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4 := by
  unfold huffman_cost_entail_wit_4
  right
  intro n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_4_split_goal_1 n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_huffman_cost_entail_wit_4_split_goal_2 n_pre weights_l total active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_huffman_cost_entail_wit_6_1_split_goal_1 : huffman_cost_entail_wit_6_1_split_goal_1 := by
  unfold huffman_cost_entail_wit_6_1_split_goal_1
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact huffman_min_scan_take_new__min_scan_updates work_l_2 i first PreH22 PreH1

theorem proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1 := by
  unfold huffman_cost_entail_wit_6_1
  right
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_6_1_split_goal_1 n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_huffman_cost_entail_wit_6_2_split_goal_1 : huffman_cost_entail_wit_6_2_split_goal_1 := by
  unfold huffman_cost_entail_wit_6_2_split_goal_1
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact huffman_min_scan_keep_old__min_scan_updates work_l_2 i first PreH22 PreH1

theorem proof_of_huffman_cost_entail_wit_6_2 : huffman_cost_entail_wit_6_2 := by
  unfold huffman_cost_entail_wit_6_2
  right
  intro n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_6_2_split_goal_1 n_pre weights_l total first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_huffman_cost_entail_wit_8_split_goal_1 : huffman_cost_entail_wit_8_split_goal_1 := by
  unfold huffman_cost_entail_wit_8_split_goal_1
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply huffman_first_held_after_removal__removals_bounds weights_l work_l first active total
  · omega
  · omega
  · have he : i = active := by omega
    simpa only [he] using PreH21
  · exact PreH20

theorem proof_of_huffman_cost_entail_wit_8_split_goal_2 : huffman_cost_entail_wit_8_split_goal_2 := by
  unfold huffman_cost_entail_wit_8_split_goal_2
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact replace_last_live_bounds__removals_bounds work_l first active 1 8000 ⟨PreH14, by omega⟩ (by omega) PreH19

theorem proof_of_huffman_cost_entail_wit_8_split_goal_3 : huffman_cost_entail_wit_8_split_goal_3 := by
  unfold huffman_cost_entail_wit_8_split_goal_3
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact (PreH19 first ⟨PreH14, by omega⟩).2

theorem proof_of_huffman_cost_entail_wit_8_split_goal_4 : huffman_cost_entail_wit_8_split_goal_4 := by
  unfold huffman_cost_entail_wit_8_split_goal_4
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact (PreH19 first ⟨PreH14, by omega⟩).1

theorem proof_of_huffman_cost_entail_wit_8_split_goal_5 : huffman_cost_entail_wit_8_split_goal_5 := by
  unfold huffman_cost_entail_wit_8_split_goal_5
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  rw [Zlength_replace_Znth]; exact PreH7

theorem proof_of_huffman_cost_entail_wit_8 : huffman_cost_entail_wit_8 := by
  unfold huffman_cost_entail_wit_8
  right
  intro n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_1 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_2 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_3 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_4 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      | exact proof_of_huffman_cost_entail_wit_8_split_goal_5 n_pre weights_l total first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_huffman_cost_entail_wit_9_split_goal_1 : huffman_cost_entail_wit_9_split_goal_1 := by
  unfold huffman_cost_entail_wit_9_split_goal_1
  intro n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact huffman_min_scan_init__min_scan_updates work_l_2

theorem proof_of_huffman_cost_entail_wit_9_split_goal_2 : huffman_cost_entail_wit_9_split_goal_2 := by
  unfold huffman_cost_entail_wit_9_split_goal_2
  intro n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH14

theorem proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9 := by
  unfold huffman_cost_entail_wit_9
  right
  intro n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_9_split_goal_1 n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_huffman_cost_entail_wit_9_split_goal_2 n_pre weights_l work_l_2 active first x total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_huffman_cost_entail_wit_10_1_split_goal_1 : huffman_cost_entail_wit_10_1_split_goal_1 := by
  unfold huffman_cost_entail_wit_10_1_split_goal_1
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact huffman_min_scan_take_new__min_scan_updates work_l_2 i second PreH24 PreH1

theorem proof_of_huffman_cost_entail_wit_10_1 : huffman_cost_entail_wit_10_1 := by
  unfold huffman_cost_entail_wit_10_1
  right
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_10_1_split_goal_1 n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_huffman_cost_entail_wit_10_2_split_goal_1 : huffman_cost_entail_wit_10_2_split_goal_1 := by
  unfold huffman_cost_entail_wit_10_2_split_goal_1
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact huffman_min_scan_keep_old__min_scan_updates work_l_2 i second PreH24 PreH1

theorem proof_of_huffman_cost_entail_wit_10_2 : huffman_cost_entail_wit_10_2 := by
  unfold huffman_cost_entail_wit_10_2
  right
  intro n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_10_2_split_goal_1 n_pre weights_l total x second first i active work_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_huffman_cost_entail_wit_12_split_goal_1 : huffman_cost_entail_wit_12_split_goal_1 := by
  unfold huffman_cost_entail_wit_12_split_goal_1
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact huffman_pair_ready_after_removal__removals_bounds weights_l work_l active x second total i n_pre
    PreH7 ⟨PreH9, PreH10⟩ ⟨PreH16, PreH17⟩ ⟨PreH3, PreH12⟩ PreH24 PreH25

theorem proof_of_huffman_cost_entail_wit_12_split_goal_2 : huffman_cost_entail_wit_12_split_goal_2 := by
  unfold huffman_cost_entail_wit_12_split_goal_2
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact replace_last_live_bounds__removals_bounds work_l second active 1 8000 ⟨PreH16, by omega⟩ (by omega) PreH23

theorem proof_of_huffman_cost_entail_wit_12_split_goal_3 : huffman_cost_entail_wit_12_split_goal_3 := by
  unfold huffman_cost_entail_wit_12_split_goal_3
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (huffman_residual_charge_bounds__removals_bounds weights_l work_l active x second total n_pre
    PreH6 PreH7 ⟨PreH4, PreH5⟩ PreH8 ⟨PreH9, PreH10⟩ ⟨PreH16, by omega⟩ PreH19 PreH24).2

theorem proof_of_huffman_cost_entail_wit_12_split_goal_4 : huffman_cost_entail_wit_12_split_goal_4 := by
  unfold huffman_cost_entail_wit_12_split_goal_4
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (huffman_residual_charge_bounds__removals_bounds weights_l work_l active x second total n_pre
    PreH6 PreH7 ⟨PreH4, PreH5⟩ PreH8 ⟨PreH9, PreH10⟩ ⟨PreH16, by omega⟩ PreH19 PreH24).1

theorem proof_of_huffman_cost_entail_wit_12_split_goal_5 : huffman_cost_entail_wit_12_split_goal_5 := by
  unfold huffman_cost_entail_wit_12_split_goal_5
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (PreH23 second ⟨PreH16, by omega⟩).2

theorem proof_of_huffman_cost_entail_wit_12_split_goal_6 : huffman_cost_entail_wit_12_split_goal_6 := by
  unfold huffman_cost_entail_wit_12_split_goal_6
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (PreH23 second ⟨PreH16, by omega⟩).1

theorem proof_of_huffman_cost_entail_wit_12_split_goal_7 : huffman_cost_entail_wit_12_split_goal_7 := by
  unfold huffman_cost_entail_wit_12_split_goal_7
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rw [Zlength_replace_Znth]; exact PreH7

theorem proof_of_huffman_cost_entail_wit_12 : huffman_cost_entail_wit_12 := by
  unfold huffman_cost_entail_wit_12
  right
  intro n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_1 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_2 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_3 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_4 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_5 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_6 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
      | exact proof_of_huffman_cost_entail_wit_12_split_goal_7 n_pre weights_l total x second first i active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_huffman_cost_entail_wit_13_split_goal_1 : huffman_cost_entail_wit_13_split_goal_1 := by
  unfold huffman_cost_entail_wit_13_split_goal_1
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  simpa only [Int.add_assoc] using huffman_progress_after_merge__merge_transition weights_l work_l_2 active x y total
    ⟨PreH6, by omega⟩ PreH20

theorem proof_of_huffman_cost_entail_wit_13_split_goal_2 : huffman_cost_entail_wit_13_split_goal_2 := by
  unfold huffman_cost_entail_wit_13_split_goal_2
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  intro k hk
  by_cases he : k = active
  · subst k
    rw [Znth_replace_Znth_Same 0 work_l_2 active _ ⟨PreH6, by omega⟩]
    omega
  · rw [Znth_replace_Znth_Diff 0 work_l_2 active k _ ⟨PreH6, by omega⟩ ⟨hk.1, by omega⟩ (Ne.symm he)]
    exact PreH19 k ⟨hk.1, by omega⟩

theorem proof_of_huffman_cost_entail_wit_13_split_goal_3 : huffman_cost_entail_wit_13_split_goal_3 := by
  unfold huffman_cost_entail_wit_13_split_goal_3
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  rw [Zlength_replace_Znth]; exact PreH4

theorem proof_of_huffman_cost_entail_wit_13 : huffman_cost_entail_wit_13 := by
  unfold huffman_cost_entail_wit_13
  right
  intro n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_13_split_goal_1 n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_huffman_cost_entail_wit_13_split_goal_2 n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
      | exact proof_of_huffman_cost_entail_wit_13_split_goal_3 n_pre weights_l work_l_2 active first second x y total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_huffman_cost_entail_wit_14_split_goal_1 : huffman_cost_entail_wit_14_split_goal_1 := by
  unfold huffman_cost_entail_wit_14_split_goal_1
  intro n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : active = 1 := by omega
  unfold HuffmanProgress HuffmanResidualOptimum at PreH12
  rw [he, sublist_zero_one__final_result work_l (by omega)] at PreH12
  unfold HuffmanScratchFinal
  simpa only [sum, List.foldr_cons, List.foldr_nil, Int.add_zero] using PreH12.1

theorem proof_of_huffman_cost_entail_wit_14_split_goal_2 : huffman_cost_entail_wit_14_split_goal_2 := by
  unfold huffman_cost_entail_wit_14_split_goal_2
  intro n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : active = 1 := by omega
  unfold HuffmanProgress HuffmanResidualOptimum at PreH12
  rw [he, sublist_zero_one__final_result work_l (by omega)] at PreH12
  obtain ⟨_, rem, ho, hi⟩ := PreH12
  have hz := huffman_singleton_optimal_zero__final_result _ rem ho
  simpa only [hz, Int.add_zero] using hi

theorem proof_of_huffman_cost_entail_wit_14 : huffman_cost_entail_wit_14 := by
  unfold huffman_cost_entail_wit_14
  right
  intro n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_huffman_cost_entail_wit_14_split_goal_1 n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_huffman_cost_entail_wit_14_split_goal_2 n_pre weights_l total active work_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

end SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_proof_manual
