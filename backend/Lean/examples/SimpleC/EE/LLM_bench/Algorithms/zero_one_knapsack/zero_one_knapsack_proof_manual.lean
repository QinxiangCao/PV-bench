import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_goal
import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open zero_one_knapsack_goal zero_one_knapsack_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem previous_cell (weights values dp : List Int) (n capacity width i j col : Int)
    (hs : KnapsackRowAnnotationState weights values n capacity width dp i j)
    (hi : 1 ≤ i) (hcol : 0 ≤ col ∧ col ≤ capacity) (hcj : col ≤ j) :
    KnapsackCellCorrect weights values (i-1) col (Znth (((i-1)*width+col)-0) dp 0) := by
  have hw := hs.1.2.2.1
  have hcap := hs.1.2.1
  have he : ((i-1)*width+col)-0 = KnapsackCellIndex capacity (i-1) col := by rw [hw]; simp [KnapsackCellIndex]
  rw [he]
  apply hs.2.2.2.2.2.2 (i-1) col (by omega) hcol
  unfold KnapsackCellIndex
  constructor
  · exact add_nonneg (mul_nonneg (by omega) (by omega)) hcol.1
  · nlinarith

theorem proof_of_zeroOneKnapsack_safety_wit_22_split_goal_1 : zeroOneKnapsack_safety_wit_22_split_goal_1 := by
  unfold zeroOneKnapsack_safety_wit_22_split_goal_1
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hs := PreH42.2.2.2.2.1
  have hb := PreH42.2.2.2.2.2.1 (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) (by rw [hs.2]; omega)
  have hv := PreH42.1.2.2.2.2.2.2.2 (i-1) ⟨PreH14, PreH15⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_22_split_goal_2 : zeroOneKnapsack_safety_wit_22_split_goal_2 := by
  unfold zeroOneKnapsack_safety_wit_22_split_goal_2
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hs := PreH42.2.2.2.2.1
  have hb := PreH42.2.2.2.2.2.1 (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) (by rw [hs.2]; omega)
  have hv := PreH42.1.2.2.2.2.2.2.2 (i-1) ⟨PreH14, PreH15⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_22 : zeroOneKnapsack_safety_wit_22 := by
  unfold zeroOneKnapsack_safety_wit_22
  right
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hs := PreH42.2.2.2.2.1
  have hb := PreH42.2.2.2.2.2.1 (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) (by rw [hs.2]; omega)
  have hv := PreH42.1.2.2.2.2.2.2.2 (i-1) ⟨PreH14, PreH15⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_29_split_goal_1 : zeroOneKnapsack_safety_wit_29_split_goal_1 := by
  unfold zeroOneKnapsack_safety_wit_29_split_goal_1
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_29_split_goal_2 : zeroOneKnapsack_safety_wit_29_split_goal_2 := by
  unfold zeroOneKnapsack_safety_wit_29_split_goal_2
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_29 : zeroOneKnapsack_safety_wit_29 := by
  unfold zeroOneKnapsack_safety_wit_29
  right
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_zeroOneKnapsack_safety_wit_30_split_goal_1 : zeroOneKnapsack_safety_wit_30_split_goal_1 := by
  unfold zeroOneKnapsack_safety_wit_30_split_goal_1
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH4.1
  have hn := mul_nonneg hp.1 (show 0 ≤ width by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_zeroOneKnapsack_safety_wit_30_split_goal_2 : zeroOneKnapsack_safety_wit_30_split_goal_2 := by
  unfold zeroOneKnapsack_safety_wit_30_split_goal_2
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH4.1
  have hn := mul_nonneg hp.1 (show 0 ≤ width by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_zeroOneKnapsack_safety_wit_30 : zeroOneKnapsack_safety_wit_30 := by
  unfold zeroOneKnapsack_safety_wit_30
  right
  intro dp_pre capacity_pre n_pre values_pre weights_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_length_range dp_pre ((n_pre+1)*(capacity_pre+1)) dp_l)
  Intros_p hsize
  change 0 ≤ (n_pre+1)*(capacity_pre+1)*4 ∧ (n_pre+1)*(capacity_pre+1)*4 ≤ 4294967296 at hsize
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH4.1
  have hn := mul_nonneg hp.1 (show 0 ≤ width by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1 := by
  unfold zeroOneKnapsack_entail_wit_1
  right
  intro dp_pre capacity_pre n_pre values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5
  have hs : KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre (capacity_pre+1) [] 0 := by
    refine ⟨⟨⟨PreH1, PreH2⟩, ⟨PreH3, PreH4⟩, rfl, ⟨by omega, by omega⟩, PreH5⟩,
      ⟨by omega, by omega⟩, ?_, ?_, ?_, ?_⟩
    · simp only [Int.zero_mul]; exact ⟨by omega, mul_nonneg (by omega) (by omega)⟩
    · simp [KnapsackTablePrefixShape, Zlength]
    · intro k hk; simp [Zlength] at hk; omega
    · intro r c hr hc hi; simp only [Int.zero_mul] at hi; omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
  simp only [Int.zero_mul]
  sep_apply (intArray.undef_full_to_undef_seg dp_pre ((n_pre+1)*(capacity_pre+1)))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (intArray.seg_empty dp_pre 0 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2 := by
  unfold zeroOneKnapsack_entail_wit_2
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hs : KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i 0 := by
    rcases PreH9 with ⟨hs, hr, htotal, hshape, hb, hd⟩
    refine ⟨hs, ⟨PreH7, PreH1⟩, ⟨by omega, by omega⟩, ?_, ?_, hb, ?_⟩
    · simpa only [Int.add_zero] using htotal
    · simpa only [Int.add_zero] using hshape
    · exact KnapsackRowsDone_to_RowProgress0 _ _ _ _ _ PreH5 hd
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  simp only [Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1 : zeroOneKnapsack_entail_wit_3_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_3_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hm := mul_le_mul_of_nonneg_right PreH20 (show 0 ≤ capacity_pre+1 by omega)
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3 := by
  unfold zeroOneKnapsack_entail_wit_3
  right
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1 capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1 : zeroOneKnapsack_entail_wit_5_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_5_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5 := by
  unfold zeroOneKnapsack_entail_wit_5
  right
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1 capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35

theorem proof_of_zeroOneKnapsack_entail_wit_6_split_goal_1 : zeroOneKnapsack_entail_wit_6_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_6_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hw := PreH40.1.2.2.2.2.2.2.1 (i-1) ⟨PreH12, PreH13⟩
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_6 : zeroOneKnapsack_entail_wit_6 := by
  unfold zeroOneKnapsack_entail_wit_6
  right
  intro capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_6_split_goal_1 capacity_pre n_pre values_l weights_l dp_l j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40

theorem proof_of_zeroOneKnapsack_entail_wit_7_1 : zeroOneKnapsack_entail_wit_7_1 := by
  unfold zeroOneKnapsack_entail_wit_7_1
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hinput := PreH24.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hcell : KnapsackCellCorrect weights_l values_l i j 0 := by
    rw [PreH1]; exact KnapsackCellCorrect_row0_zero _ _ _ PreH22 hlen
  have hv : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 4000000 := ⟨by omega, by omega⟩
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH24 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(0 : Int)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_2 : zeroOneKnapsack_entail_wit_7_2 := by
  unfold zeroOneKnapsack_entail_wit_7_2
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hinput := PreH25.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hcell : KnapsackCellCorrect weights_l values_l i j 0 := by
    rw [PreH1]
    apply KnapsackCellCorrect_col0_zero _ _ _ ⟨PreH21, by rw [hinput.1]; omega⟩ hlen
    intro k hk
    exact (hinput.2.2.1 k ⟨hk.1, by omega⟩).1
  have hv : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 4000000 := ⟨by omega, by omega⟩
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH25 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(0 : Int)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_3 : zeroOneKnapsack_entail_wit_7_3 := by
  unfold zeroOneKnapsack_entail_wit_7_3
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  have hinput := PreH43.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hnonneg : ∀ k, (0 ≤ k ∧ k < Zlength weights_l) → 0 ≤ Znth k weights_l 0 := by
    intro k hk; have hh := hinput.2.2.1 k ⟨hk.1, by rw [← hinput.1]; exact hk.2⟩; omega
  have ho := previous_cell _ _ _ _ _ _ _ _ j PreH43 (by omega) ⟨by omega, by omega⟩ (by omega)
  have hw := hinput.2.2.1 (i-1) ⟨PreH15, PreH16⟩
  have hp := previous_cell _ _ _ _ _ _ _ _ (j-Znth (i-1) weights_l 0) PreH43
    (by omega) ⟨by omega, by omega⟩ (by omega)
  have hc := KnapsackCellCorrect_take_better _ _ (i-1) j (Znth (i-1) weights_l 0)
    (Znth (i-1) values_l 0) _ _ ⟨PreH15, by rw [hinput.1]; omega⟩ hlen rfl rfl (by omega) hnonneg ho hp PreH1
  have hcell := hc
  rw [show i-1+1 = i by omega] at hcell
  have hv := KnapsackCellCorrect_value_bound _ _ _ _ _ n_pre hinput.2.1
    ⟨by omega, by omega⟩ hinput.2.2.2 hcell
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH43 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(Znth (((i-1)*width+(j-Znth (i-1) weights_l 0))-0) dp_l_2 0 + Znth (i-1) values_l 0)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_4 : zeroOneKnapsack_entail_wit_7_4 := by
  unfold zeroOneKnapsack_entail_wit_7_4
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  have hinput := PreH43.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hnonneg : ∀ k, (0 ≤ k ∧ k < Zlength weights_l) → 0 ≤ Znth k weights_l 0 := by
    intro k hk; have hh := hinput.2.2.1 k ⟨hk.1, by rw [← hinput.1]; exact hk.2⟩; omega
  have ho := previous_cell _ _ _ _ _ _ _ _ j PreH43 (by omega) ⟨by omega, by omega⟩ (by omega)
  have hw := hinput.2.2.1 (i-1) ⟨PreH15, PreH16⟩
  have hp := previous_cell _ _ _ _ _ _ _ _ (j-Znth (i-1) weights_l 0) PreH43
    (by omega) ⟨by omega, by omega⟩ (by omega)
  have hc := KnapsackCellCorrect_keep_without_when_better_or_equal _ _ (i-1) j (Znth (i-1) weights_l 0)
    (Znth (i-1) values_l 0) _ _ ⟨PreH15, by rw [hinput.1]; omega⟩ hlen rfl rfl (by omega) hnonneg ho hp PreH1
  have hcell := hc
  rw [show i-1+1 = i by omega] at hcell
  have hv := KnapsackCellCorrect_value_bound _ _ _ _ _ n_pre hinput.2.1
    ⟨by omega, by omega⟩ hinput.2.2.2 hcell
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH43 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(Znth (((i-1)*width+j)-0) dp_l_2 0)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_7_5 : zeroOneKnapsack_entail_wit_7_5 := by
  unfold zeroOneKnapsack_entail_wit_7_5
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hinput := PreH38.1.2.2.2.2
  have hlen : Zlength weights_l = Zlength values_l := by rw [hinput.1, hinput.2.1]
  have hnonneg : ∀ k, (0 ≤ k ∧ k < Zlength weights_l) → 0 ≤ Znth k weights_l 0 := by
    intro k hk; have hh := hinput.2.2.1 k ⟨hk.1, by rw [← hinput.1]; exact hk.2⟩; omega
  have ho := previous_cell _ _ _ _ _ _ _ _ j PreH38 (by omega) ⟨by omega, by omega⟩ (by omega)
  have hc := KnapsackCellCorrect_too_heavy _ _ (i-1) j (Znth (i-1) weights_l 0)
    (Znth (i-1) values_l 0) _ ⟨PreH10, by rw [hinput.1]; omega⟩ hlen rfl rfl PreH1 hnonneg ho
  have hcell := hc
  rw [show i-1+1 = i by omega] at hcell
  have hv := KnapsackCellCorrect_value_bound _ _ _ _ _ n_pre hinput.2.1
    ⟨by omega, by omega⟩ hinput.2.2.2 hcell
  have hs := KnapsackRowAnnotationState_append_cell__row_state_result_refactor _ _ _ _ _ _ _ _ _
    PreH38 ⟨by omega, by omega⟩ hcell hv
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (dp_l_2++[(Znth (((i-1)*width+j)-0) dp_l_2 0)]) ?_
  rw [show i*width+(j+1) = i*width+j+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8 := by
  unfold zeroOneKnapsack_entail_wit_8
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 j i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hj : j = capacity_pre+1 := by omega
  have he : (i+1)*width = i*width+j := by nlinarith
  have hs : KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 (i+1) := by
    rcases PreH11 with ⟨hs, hr, hc, htotal, hshape, hb, hp⟩
    refine ⟨hs, ⟨by omega, by omega⟩, ?_, ?_, hb, ?_⟩
    · rw [he]; exact htotal
    · rw [he]; exact hshape
    · exact KnapsackRowProgress_end_to_RowsDone _ _ _ _ _ _ hj hp
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  rw [he]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9 := by
  unfold zeroOneKnapsack_entail_wit_9
  right
  intro dp_pre capacity_pre n_pre values_l weights_l dp_l_2 i width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hi : i = n_pre+1 := by omega
  have hs := KnapsackRowsAnnotationState_to_Result__row_state_result_refactor _ _ _ _ _ _ (by rw [← hi]; exact PreH9)
  have he : i*width = (n_pre+1)*(capacity_pre+1) := by rw [hi, PreH2]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  rw [he]
  split_pure_spatial
  · sep_apply (intArray.seg_to_full dp_pre 0 ((n_pre+1)*(capacity_pre+1)) dp_l_2)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    sep_apply (intArray.undef_seg_empty dp_pre ((n_pre+1)*(capacity_pre+1)))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_zeroOneKnapsack_entail_wit_10_split_goal_1 : zeroOneKnapsack_entail_wit_10_split_goal_1 := by
  unfold zeroOneKnapsack_entail_wit_10_split_goal_1
  intro capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH8.1
  have hm := mul_nonneg hp.1 (show 0 ≤ capacity_pre+1 by omega)
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_10_split_goal_2 : zeroOneKnapsack_entail_wit_10_split_goal_2 := by
  unfold zeroOneKnapsack_entail_wit_10_split_goal_2
  intro capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hp := KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit _ _ _ _ _ PreH8.1
  have hm := mul_nonneg hp.1 (show 0 ≤ capacity_pre+1 by omega)
  nlinarith

theorem proof_of_zeroOneKnapsack_entail_wit_10 : zeroOneKnapsack_entail_wit_10 := by
  unfold zeroOneKnapsack_entail_wit_10
  right
  intro capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_zeroOneKnapsack_entail_wit_10_split_goal_1 capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_zeroOneKnapsack_entail_wit_10_split_goal_2 capacity_pre n_pre values_l weights_l dp_l width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

end SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_proof_manual
