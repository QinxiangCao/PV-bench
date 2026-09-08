import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_goal
import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open multiple_knapsack_goal multiple_knapsack_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem queue_drop_pack (old qi qv : List Int) (head tail r w v cnt k cap : Int)
    (hs : MKQueueDropSafety old qi qv head tail r w k cap)
    (hm : MKQueueDropSemantics old qi qv head tail r w v cnt k) :
    MKQueueDropLoopState old qi qv head tail r w v cnt k cap := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩ := hs
  exact ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hm⟩
private theorem queue_pending_pack (old qi qv : List Int) (head tail r w v cnt k cap current : Int)
    (hs : MKQueueDropSafety old qi qv head tail r w k cap)
    (hm : MKQueuePendingSemantics old qi qv head tail r w v cnt k current) :
    MKQueuePendingState old qi qv head tail r w v cnt k cap current := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩ := hs
  exact ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hm⟩

theorem proof_of_multipleKnapsack_safety_wit_12_split_goal_1 : multipleKnapsack_safety_wit_12_split_goal_1 := by
  unfold multipleKnapsack_safety_wit_12_split_goal_1
  intro q_val_pre q_idx_pre old_pre dp_pre capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hb := PreH38.2 pos ⟨by omega,by omega⟩
  dump_pre_spatial
  change Znth pos old_l 0-k*v ≤ 2147483647
  nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ v by omega)]

theorem proof_of_multipleKnapsack_safety_wit_12_split_goal_2 : multipleKnapsack_safety_wit_12_split_goal_2 := by
  unfold multipleKnapsack_safety_wit_12_split_goal_2
  intro q_val_pre q_idx_pre old_pre dp_pre capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hb := PreH38.2 pos ⟨by omega,by omega⟩
  dump_pre_spatial
  change -2147483648 ≤ Znth pos old_l 0-k*v
  nlinarith [mul_le_mul_of_nonneg_left (show v ≤ 1000 by omega) (show 0 ≤ k by omega)]

theorem proof_of_multipleKnapsack_entail_wit_1_split_goal_1 : multipleKnapsack_entail_wit_1_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_1_split_goal_1
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH9

theorem proof_of_multipleKnapsack_entail_wit_1_split_goal_2 : multipleKnapsack_entail_wit_1_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_1_split_goal_2
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  intro cap hcap
  omega

theorem proof_of_multipleKnapsack_entail_wit_1_split_goal_3 : multipleKnapsack_entail_wit_1_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_1_split_goal_3
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact ⟨le_refl _,rfl⟩

theorem proof_of_multipleKnapsack_entail_wit_1_split_goal_4 : multipleKnapsack_entail_wit_1_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_1_split_goal_4
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rfl

theorem proof_of_multipleKnapsack_entail_wit_2_split_goal_1 : multipleKnapsack_entail_wit_2_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_2_split_goal_1
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact (MKZeroPrefix_extend_by_zero dp_l_2 j ⟨PreH13.1,PreH13.2,PreH14⟩).2.2

theorem proof_of_multipleKnapsack_entail_wit_2_split_goal_2 : multipleKnapsack_entail_wit_2_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_2_split_goal_2
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have h := MKZeroPrefix_extend_by_zero dp_l_2 j ⟨PreH13.1,PreH13.2,PreH14⟩
  exact ⟨h.1,h.2.1⟩

theorem proof_of_multipleKnapsack_entail_wit_2_split_goal_3 : multipleKnapsack_entail_wit_2_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_2_split_goal_3
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_multipleKnapsack_entail_wit_4_split_goal_1 : multipleKnapsack_entail_wit_4_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_4_split_goal_1
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH14

theorem proof_of_multipleKnapsack_entail_wit_4_split_goal_2 : multipleKnapsack_entail_wit_4_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_4_split_goal_2
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH9.2.2

theorem proof_of_multipleKnapsack_entail_wit_4_split_goal_3 : multipleKnapsack_entail_wit_4_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_4_split_goal_3
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH9.2.1

theorem proof_of_multipleKnapsack_entail_wit_4_split_goal_4 : multipleKnapsack_entail_wit_4_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_4_split_goal_4
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH9.1

theorem proof_of_multipleKnapsack_entail_wit_5_split_goal_1 : multipleKnapsack_entail_wit_5_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_5_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH17

theorem proof_of_multipleKnapsack_entail_wit_5_split_goal_2 : multipleKnapsack_entail_wit_5_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_5_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro cap hcap
  omega

theorem proof_of_multipleKnapsack_entail_wit_5_split_goal_3 : multipleKnapsack_entail_wit_5_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_5_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact ⟨⟨by omega,by omega⟩,by assumption,by assumption⟩

theorem proof_of_multipleKnapsack_entail_wit_6_split_goal_1 : multipleKnapsack_entail_wit_6_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_6_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hc : MKCopyPrefix dp_l_2 old_l_2 j capacity_pre := ⟨PreH19.1,PreH19.2.1,PreH19.2.2,PreH20⟩
  have hs := MKCopyPrefix_extend_by_replace_Znth dp_l_2 old_l_2 j capacity_pre hc (by omega)
  exact hs.2.2.2

theorem proof_of_multipleKnapsack_entail_wit_6_split_goal_2 : multipleKnapsack_entail_wit_6_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_6_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hc : MKCopyPrefix dp_l_2 old_l_2 j capacity_pre := ⟨PreH19.1,PreH19.2.1,PreH19.2.2,PreH20⟩
  have hs := MKCopyPrefix_extend_by_replace_Znth dp_l_2 old_l_2 j capacity_pre hc (by omega)
  exact ⟨hs.1,hs.2.1,hs.2.2.1⟩

theorem proof_of_multipleKnapsack_entail_wit_6_split_goal_3 : multipleKnapsack_entail_wit_6_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_6_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  rw [Zlength_replace_Znth]
  assumption

theorem proof_of_multipleKnapsack_entail_wit_7_split_goal_1 : multipleKnapsack_entail_wit_7_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_7_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_multipleKnapsack_entail_wit_7_split_goal_2 : multipleKnapsack_entail_wit_7_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_7_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  refine ⟨?_,?_⟩
  · intro rem k pos hpos hrem; omega
  · intro rem k pos he hrem hk hp
    exact (PreH20 pos ⟨hp.1,by omega⟩).symm

theorem proof_of_multipleKnapsack_entail_wit_7_split_goal_3 : multipleKnapsack_entail_wit_7_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_7_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hitem := PreH21 i ⟨by omega,by omega⟩
  exact ⟨by omega,by omega,by omega,by omega,by omega,PreH19.2.2,PreH19.2.1⟩

theorem proof_of_multipleKnapsack_entail_wit_7_split_goal_4 : multipleKnapsack_entail_wit_7_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_7_split_goal_4
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have he : j = capacity_pre+1 := by omega
  exact he ▸ PreH20

theorem proof_of_multipleKnapsack_entail_wit_7_split_goal_5 : multipleKnapsack_entail_wit_7_split_goal_5 := by
  unfold multipleKnapsack_entail_wit_7_split_goal_5
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have he : j = capacity_pre+1 := by omega
  exact he ▸ PreH19

theorem proof_of_multipleKnapsack_entail_wit_7_split_goal_6 : multipleKnapsack_entail_wit_7_split_goal_6 := by
  unfold multipleKnapsack_entail_wit_7_split_goal_6
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hd := MKDPTable_from_safety_semantics__g10 weights_l values_l counts_l i capacity_pre dp_l_2 PreH17 PreH18
  have he : j = capacity_pre+1 := by omega
  have hcopy : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre+1) capacity_pre := by
    rw [← he]; exact ⟨PreH19.1,PreH19.2.1,PreH19.2.2,PreH20⟩
  have hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights_l) → 1 ≤ Znth idx weights_l 0 ∧ 0 ≤ Znth idx values_l 0 ∧ Znth idx values_l 0 ≤ 1000 := by
    intro idx hidx
    have h := PreH21 idx ⟨hidx.1,by omega⟩
    exact ⟨h.1.1.1.1.1,h.1.1.1.2,h.1.1.2⟩
  have hitem := hb i ⟨by omega,by omega⟩
  exact MKDPTable_implies_MKTransitionValueBound_for_current_item weights_l values_l counts_l i capacity_pre dp_l_2 old_l_2 _ _ _ ⟨by omega,by omega⟩ hitem.1 hitem.2 hb hd hcopy

theorem proof_of_multipleKnapsack_entail_wit_7_split_goal_7 : multipleKnapsack_entail_wit_7_split_goal_7 := by
  unfold multipleKnapsack_entail_wit_7_split_goal_7
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hd := MKDPTable_from_safety_semantics__g10 weights_l values_l counts_l i capacity_pre dp_l_2 PreH17 PreH18
  have he : j = capacity_pre+1 := by omega
  have hcopy : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre+1) capacity_pre := by
    rw [← he]; exact ⟨PreH19.1,PreH19.2.1,PreH19.2.2,PreH20⟩
  have hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights_l) → 1 ≤ Znth idx weights_l 0 ∧ 0 ≤ Znth idx values_l 0 ∧ Znth idx values_l 0 ≤ 1000 := by
    intro idx hidx
    have h := PreH21 idx ⟨hidx.1,by omega⟩
    exact ⟨h.1.1.1.1.1,h.1.1.1.2,h.1.1.2⟩
  exact MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds weights_l values_l counts_l i capacity_pre dp_l_2 old_l_2 ⟨by omega,by omega⟩ hb hd hcopy

theorem proof_of_multipleKnapsack_entail_wit_8_split_goal_1 : multipleKnapsack_entail_wit_8_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_8_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact PreH31

theorem proof_of_multipleKnapsack_entail_wit_8_split_goal_2 : multipleKnapsack_entail_wit_8_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_8_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  intro cap hcap
  rw [PreH28 cap ⟨hcap.1,by omega⟩]
  exact PreH24 cap hcap

theorem proof_of_multipleKnapsack_entail_wit_8_split_goal_3 : multipleKnapsack_entail_wit_8_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_8_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  exact ⟨PreH23.1,PreH23.2.1,PreH27.2.2⟩

theorem proof_of_multipleKnapsack_entail_wit_9_split_goal_1 : multipleKnapsack_entail_wit_9_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_9_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact PreH34

theorem proof_of_multipleKnapsack_entail_wit_9_split_goal_2 : multipleKnapsack_entail_wit_9_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_9_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  dsimp only [MKResidueLoopSemantics,MKQueueResultSemantics,MKQueueEntriesValidForResult,MKQueueIndexIncreasing,MKQueueValueDecreasing,MKQueueCoversResultWindow,MKQueueResultValueBound]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> intros <;> omega

theorem proof_of_multipleKnapsack_entail_wit_9_split_goal_3 : multipleKnapsack_entail_wit_9_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_9_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  obtain ⟨hw,hcnt,hr,hrw,hrc,ho,hd⟩ := PreH32
  exact ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,by omega,ho,hd,by assumption,by assumption⟩

theorem proof_of_multipleKnapsack_entail_wit_9_split_goal_4 : multipleKnapsack_entail_wit_9_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_9_split_goal_4
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  refine ⟨?_,?_⟩
  · intro t ht; omega
  · intro pos hp
    exact ⟨fun rem t he hr ht => PreH33.1 rem t pos he hr ht hp,
      fun rem t he hr ht hcase => PreH33.2 rem t pos he ⟨by omega,hr.2⟩ ht hp⟩

theorem proof_of_multipleKnapsack_entail_wit_9_split_goal_5 : multipleKnapsack_entail_wit_9_split_goal_5 := by
  unfold multipleKnapsack_entail_wit_9_split_goal_5
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  obtain ⟨hw,hcnt,hr,hrw,hrc,ho,hd⟩ := PreH32
  exact ⟨hw,hcnt,⟨by omega,by omega⟩,by omega,by omega,ho,hd⟩

theorem proof_of_multipleKnapsack_entail_wit_10_split_goal_1 : multipleKnapsack_entail_wit_10_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_10_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  exact PreH44

theorem proof_of_multipleKnapsack_entail_wit_10_split_goal_2 : multipleKnapsack_entail_wit_10_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_10_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  obtain ⟨hv,hi,hd,hc,hb,ht⟩ := PreH43.2
  exact ⟨hv,hi,hd,fun cand h0 hk hlo hl => hc cand h0 hk (by omega) hl,hb⟩

theorem proof_of_multipleKnapsack_entail_wit_10_split_goal_3 : multipleKnapsack_entail_wit_10_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_10_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  obtain ⟨hr,hk,hh,ht,ho,hd,hqi,hqv⟩ := PreH42
  exact ⟨hr,hk,hh,ht,by omega,hqi,hqv,ho⟩

theorem proof_of_multipleKnapsack_entail_wit_10_split_goal_4 : multipleKnapsack_entail_wit_10_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_10_split_goal_4
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hb := PreH38.2 pos ⟨by omega,by omega⟩
  rw [← PreH27]
  nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ v by omega),
    mul_le_mul_of_nonneg_left (show 1 ≤ w by omega) (show 0 ≤ k by omega),
    mul_le_mul_of_nonneg_left (show v ≤ 1000 by omega) (show 0 ≤ k by omega)]

theorem proof_of_multipleKnapsack_entail_wit_10_split_goal_5 : multipleKnapsack_entail_wit_10_split_goal_5 := by
  unfold multipleKnapsack_entail_wit_10_split_goal_5
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hb := PreH38.2 pos ⟨by omega,by omega⟩
  rw [← PreH27]
  nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ v by omega),
    mul_le_mul_of_nonneg_left (show 1 ≤ w by omega) (show 0 ≤ k by omega),
    mul_le_mul_of_nonneg_left (show v ≤ 1000 by omega) (show 0 ≤ k by omega)]

theorem proof_of_multipleKnapsack_entail_wit_10_split_goal_6 : multipleKnapsack_entail_wit_10_split_goal_6 := by
  unfold multipleKnapsack_entail_wit_10_split_goal_6
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hb := PreH38.2 pos ⟨by omega,by omega⟩
  rw [← PreH27]
  nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ v by omega),
    mul_le_mul_of_nonneg_left (show 1 ≤ w by omega) (show 0 ≤ k by omega),
    mul_le_mul_of_nonneg_left (show v ≤ 1000 by omega) (show 0 ≤ k by omega)]

theorem proof_of_multipleKnapsack_entail_wit_10_split_goal_7 : multipleKnapsack_entail_wit_10_split_goal_7 := by
  unfold multipleKnapsack_entail_wit_10_split_goal_7
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hb := PreH38.2 pos ⟨by omega,by omega⟩
  rw [← PreH27]
  nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ v by omega),
    mul_le_mul_of_nonneg_left (show 1 ≤ w by omega) (show 0 ≤ k by omega),
    mul_le_mul_of_nonneg_left (show v ≤ 1000 by omega) (show 0 ≤ k by omega)]

theorem proof_of_multipleKnapsack_entail_wit_11_split_goal_1 : multipleKnapsack_entail_wit_11_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_11_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  obtain ⟨hv,hi,hd,hc,hb⟩ := PreH49
  refine ⟨fun p hp => hv p ⟨by omega,hp.2⟩,
    fun p q hp => hi p q ⟨by omega,hp.2⟩,
    fun p q hp => hd p q ⟨by omega,hp.2⟩,?_,fun p hp => hb p ⟨by omega,hp.2⟩⟩
  intro cand h0 hk hlo hl
  obtain ⟨p,hp,hcp,hpk,hval⟩ := hc cand h0 hk hlo hl
  refine ⟨p,⟨?_,hp.2⟩,hcp,hpk,hval⟩
  by_cases he : p = head
  · rw [he] at hcp; omega
  · omega

theorem proof_of_multipleKnapsack_entail_wit_11_split_goal_2 : multipleKnapsack_entail_wit_11_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_11_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩ := PreH48
  exact ⟨hr,hk,⟨by omega,by omega⟩,ht,htl,hqi,hqv,ho⟩

theorem proof_of_multipleKnapsack_entail_wit_12_1_split_goal_1 : multipleKnapsack_entail_wit_12_1_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_12_1_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  exact PreH49

theorem proof_of_multipleKnapsack_entail_wit_12_1_split_goal_2 : multipleKnapsack_entail_wit_12_1_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_12_1_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have he : head ≥ tail := by omega
  dsimp only [MKQueueAfterDropSemantics,MKQueueEntriesValidAfterDrop,MKQueueIndexIncreasing,MKQueueValueDecreasing,MKQueueCoversWindow,MKQueueResultValueBound]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals try (intros; omega)
  intro cand h0 hk hlo hl
  exact PreH48.2.2.2.1 cand h0 hk hlo hl

theorem proof_of_multipleKnapsack_entail_wit_12_2_split_goal_1 : multipleKnapsack_entail_wit_12_2_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_12_2_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  exact PreH50

theorem proof_of_multipleKnapsack_entail_wit_12_2_split_goal_2 : multipleKnapsack_entail_wit_12_2_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_12_2_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have hs := queue_drop_pack old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre PreH48 PreH49
  have ha := MKQueueDropLoopState_nonempty_exit_to_MKQueueAfterDrop old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH1 PreH2 PreH24 PreH16 PreH17 PreH22 PreH28 ⟨by omega,by omega⟩ PreH33 PreH37 PreH45 hs
  exact ha.2.2.2.2.2.2.2.2

theorem proof_of_multipleKnapsack_entail_wit_13_split_goal_1 : multipleKnapsack_entail_wit_13_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_13_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  exact PreH49

theorem proof_of_multipleKnapsack_entail_wit_13_split_goal_2 : multipleKnapsack_entail_wit_13_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_13_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  obtain ⟨hv,hi,hd,hc,hb⟩ := PreH48
  exact ⟨hv,hi,hd,fun cand h0 hk hlo hl => Or.inl (hc cand h0 hk hlo hl),hb,by constructor <;> omega⟩

theorem proof_of_multipleKnapsack_entail_wit_14_split_goal_1 : multipleKnapsack_entail_wit_14_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_14_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hs := queue_pending_pack old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current PreH49 PreH50
  have h := MKQueuePendingState_pop_dominated_tail_preserves old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current hs (by omega) (by omega)
  exact h.2.2.2.2.2.2.2.2

theorem proof_of_multipleKnapsack_entail_wit_14_split_goal_2 : multipleKnapsack_entail_wit_14_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_14_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩ := PreH49
  exact ⟨hr,hk,⟨hh.1,by omega⟩,by omega,by omega,hqi,hqv,ho⟩

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_1 : multipleKnapsack_entail_wit_15_1_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  exact PreH50

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_2 : multipleKnapsack_entail_wit_15_1_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 ⟨by omega,by omega⟩ PreH25 PreH29 (by intro hn; omega)
  have hh := h.2.2.1.2
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_3 : multipleKnapsack_entail_wit_15_1_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 ⟨by omega,by omega⟩ PreH25 PreH29 (by intro hn; omega)
  have hh := h.2.2.1.1
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_4 : multipleKnapsack_entail_wit_15_1_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_4
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 ⟨by omega,by omega⟩ PreH25 PreH29 (by intro hn; omega)
  have hh := h.2.2.2.2
  rw [PreH27] at hh
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_5 : multipleKnapsack_entail_wit_15_1_split_goal_5 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_5
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 ⟨by omega,by omega⟩ PreH25 PreH29 (by intro hn; omega)
  have hh := h.2.2.2.1
  rw [PreH27] at hh
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_6 : multipleKnapsack_entail_wit_15_1_split_goal_6 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_6
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 ⟨by omega,by omega⟩ PreH25 PreH29 (by intro hn; omega)
  have hh := h.2.1
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_7 : multipleKnapsack_entail_wit_15_1_split_goal_7 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_7
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 ⟨by omega,by omega⟩ PreH25 PreH29 (by intro hn; omega)
  have hh := h.1
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_8 : multipleKnapsack_entail_wit_15_1_split_goal_8 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_8
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  rw [Zlength_replace_Znth]
  assumption

theorem proof_of_multipleKnapsack_entail_wit_15_1_split_goal_9 : multipleKnapsack_entail_wit_15_1_split_goal_9 := by
  unfold multipleKnapsack_entail_wit_15_1_split_goal_9
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  rw [Zlength_replace_Znth]
  assumption

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_1 : multipleKnapsack_entail_wit_15_2_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  exact PreH51

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_2 : multipleKnapsack_entail_wit_15_2_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 ⟨by omega,by omega⟩ PreH26 PreH30 (by intro hn; omega)
  have hh := h.2.2.1.2
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_3 : multipleKnapsack_entail_wit_15_2_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 ⟨by omega,by omega⟩ PreH26 PreH30 (by intro hn; omega)
  have hh := h.2.2.1.1
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_4 : multipleKnapsack_entail_wit_15_2_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_4
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 ⟨by omega,by omega⟩ PreH26 PreH30 (by intro hn; omega)
  have hh := h.2.2.2.2
  rw [PreH28] at hh
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_5 : multipleKnapsack_entail_wit_15_2_split_goal_5 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_5
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 ⟨by omega,by omega⟩ PreH26 PreH30 (by intro hn; omega)
  have hh := h.2.2.2.1
  rw [PreH28] at hh
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_6 : multipleKnapsack_entail_wit_15_2_split_goal_6 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_6
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 ⟨by omega,by omega⟩ PreH26 PreH30 (by intro hn; omega)
  have hh := h.2.1
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_7 : multipleKnapsack_entail_wit_15_2_split_goal_7 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_7
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have h := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 ⟨by omega,by omega⟩ PreH26 PreH30 (by intro hn; omega)
  have hh := h.1
  exact hh

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_8 : multipleKnapsack_entail_wit_15_2_split_goal_8 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_8
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  rw [Zlength_replace_Znth]
  assumption

theorem proof_of_multipleKnapsack_entail_wit_15_2_split_goal_9 : multipleKnapsack_entail_wit_15_2_split_goal_9 := by
  unfold multipleKnapsack_entail_wit_15_2_split_goal_9
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  rw [Zlength_replace_Znth]
  assumption

theorem proof_of_multipleKnapsack_entail_wit_16_split_goal_1 : multipleKnapsack_entail_wit_16_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_16_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  exact PreH52

theorem proof_of_multipleKnapsack_entail_wit_16_split_goal_2 : multipleKnapsack_entail_wit_16_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_16_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have h := MKResidueLoopSemantics_after_dp_write__g09 old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre pos (Znth head qval_l_2 0+k*v) PreH14 (by omega) PreH26 ⟨by omega,by omega⟩ PreH8 PreH45 PreH47 PreH49
  rw [PreH26] at h
  exact h

theorem proof_of_multipleKnapsack_entail_wit_16_split_goal_3 : multipleKnapsack_entail_wit_16_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_16_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have h := MKResidueLoopSafety_after_dp_write__g09 old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre pos (Znth head qval_l_2 0+k*v) PreH8 PreH46
  rw [PreH26] at h
  exact h

theorem proof_of_multipleKnapsack_entail_wit_16_split_goal_4 : multipleKnapsack_entail_wit_16_split_goal_4 := by
  unfold multipleKnapsack_entail_wit_16_split_goal_4
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have h := MKItemResiduePrefixSemantics_after_dp_write__g09 old_l_2 dp_l_2 r w v cnt k capacity_pre pos (Znth head qval_l_2 0+k*v) (by omega) PreH14 PreH15 PreH26 ⟨by omega,by omega⟩ PreH8 PreH45 PreH49
  rw [PreH26] at h
  exact h

theorem proof_of_multipleKnapsack_entail_wit_16_split_goal_5 : multipleKnapsack_entail_wit_16_split_goal_5 := by
  unfold multipleKnapsack_entail_wit_16_split_goal_5
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have h := MKItemResiduePrefixSafety_after_dp_write__g09 old_l_2 dp_l_2 r w cnt k capacity_pre pos (Znth head qval_l_2 0+k*v) PreH8 PreH44
  rw [PreH26] at h
  exact h

theorem proof_of_multipleKnapsack_entail_wit_16_split_goal_6 : multipleKnapsack_entail_wit_16_split_goal_6 := by
  unfold multipleKnapsack_entail_wit_16_split_goal_6
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  ring

theorem proof_of_multipleKnapsack_entail_wit_16_split_goal_7 : multipleKnapsack_entail_wit_16_split_goal_7 := by
  unfold multipleKnapsack_entail_wit_16_split_goal_7
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  rw [Zlength_replace_Znth]
  exact PreH8

theorem proof_of_multipleKnapsack_entail_wit_17_split_goal_1 : multipleKnapsack_entail_wit_17_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_17_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  exact PreH44

theorem proof_of_multipleKnapsack_entail_wit_17_split_goal_2 : multipleKnapsack_entail_wit_17_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_17_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  apply MKItemResidueProgressSemantics_next_residue__g09 old_l_2 dp_l_2 r w v cnt k capacity_pre pos <;> first | assumption | omega

theorem proof_of_multipleKnapsack_entail_wit_17_split_goal_3 : multipleKnapsack_entail_wit_17_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_17_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  apply MKItemResidueProgressSafety_next_residue__g09 old_l_2 dp_l_2 r w cnt k capacity_pre pos <;> assumption

theorem proof_of_multipleKnapsack_entail_wit_18_split_goal_1 : multipleKnapsack_entail_wit_18_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_18_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt k head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  exact PreH38

theorem proof_of_multipleKnapsack_entail_wit_19_split_goal_1 : multipleKnapsack_entail_wit_19_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_19_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  exact PreH33

theorem proof_of_multipleKnapsack_entail_wit_19_split_goal_2 : multipleKnapsack_entail_wit_19_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_19_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hwpos : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights_l) → 1 ≤ Znth idx weights_l 0 := by
    intro idx hidx
    have h := PreH33 idx ⟨hidx.1,by omega⟩
    exact h.1.1.1.1.1
  have h := MKItemResidue_complete_table__g09 weights_l values_l counts_l i capacity_pre old_l_2 dp_l_2 r w v cnt
    ⟨by omega,by omega⟩ (by omega) (by omega) PreH15 PreH16 PreH17 hwpos PreH1 PreH27 PreH28 PreH31 PreH32
  exact h.2

theorem proof_of_multipleKnapsack_entail_wit_19_split_goal_3 : multipleKnapsack_entail_wit_19_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_19_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hwpos : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights_l) → 1 ≤ Znth idx weights_l 0 := by
    intro idx hidx
    have h := PreH33 idx ⟨hidx.1,by omega⟩
    exact h.1.1.1.1.1
  have h := MKItemResidue_complete_table__g09 weights_l values_l counts_l i capacity_pre old_l_2 dp_l_2 r w v cnt
    ⟨by omega,by omega⟩ (by omega) (by omega) PreH15 PreH16 PreH17 hwpos PreH1 PreH27 PreH28 PreH31 PreH32
  exact h.1

theorem proof_of_multipleKnapsack_entail_wit_20_split_goal_1 : multipleKnapsack_entail_wit_20_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_20_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact PreH25

theorem proof_of_multipleKnapsack_entail_wit_21_split_goal_1 : multipleKnapsack_entail_wit_21_split_goal_1 := by
  unfold multipleKnapsack_entail_wit_21_split_goal_1
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : i = n_pre := by omega
  apply MKDPTable_final_capacity_implies_MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre dp_l_2 n_pre
  · assumption
  · assumption
  · assumption
  · omega
  · rw [← he]
    exact MKDPTable_from_safety_semantics__g10 weights_l values_l counts_l i capacity_pre dp_l_2 PreH15 PreH16

theorem proof_of_multipleKnapsack_entail_wit_21_split_goal_2 : multipleKnapsack_entail_wit_21_split_goal_2 := by
  unfold multipleKnapsack_entail_wit_21_split_goal_2
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : i = n_pre := by omega
  exact he ▸ PreH16

theorem proof_of_multipleKnapsack_entail_wit_21_split_goal_3 : multipleKnapsack_entail_wit_21_split_goal_3 := by
  unfold multipleKnapsack_entail_wit_21_split_goal_3
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : i = n_pre := by omega
  exact he ▸ PreH15

theorem proof_of_multipleKnapsack_safety_wit_12 : multipleKnapsack_safety_wit_12 := by
  unfold multipleKnapsack_safety_wit_12
  right
  intro q_val_pre q_idx_pre old_pre dp_pre capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  split_pures
  all_goals first
    | exact (proof_of_multipleKnapsack_safety_wit_12_split_goal_1 q_val_pre q_idx_pre old_pre dp_pre capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
    | exact (proof_of_multipleKnapsack_safety_wit_12_split_goal_2 q_val_pre q_idx_pre old_pre dp_pre capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)

theorem proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1 := by
  unfold multipleKnapsack_entail_wit_1
  right
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_1_split_goal_1 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
      | exact (proof_of_multipleKnapsack_entail_wit_1_split_goal_2 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
      | exact (proof_of_multipleKnapsack_entail_wit_1_split_goal_3 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
      | exact (proof_of_multipleKnapsack_entail_wit_1_split_goal_4 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2 := by
  unfold multipleKnapsack_entail_wit_2
  right
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_2_split_goal_1 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
      | exact (proof_of_multipleKnapsack_entail_wit_2_split_goal_2 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
      | exact (proof_of_multipleKnapsack_entail_wit_2_split_goal_3 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

theorem proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3 := by
  unfold multipleKnapsack_entail_wit_3
  right
  intro dp_pre capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have he : j = capacity_pre+1 := by omega
  have hz : MKZeroPrefix dp_l_2 (capacity_pre+1) := by rw [← he]; exact ⟨PreH13.1,PreH13.2,PreH14⟩
  have htable := MKZeroPrefix_implies_MKDPTable_zero_items weights_l values_l counts_l capacity_pre dp_l_2 PreH4 hz
  have hsafe : MKDPTableSafety weights_l 0 capacity_pre dp_l_2 := ⟨htable.1,htable.2.1,htable.2.2.1⟩
  have hsem : MKDPTableSemantics weights_l values_l counts_l 0 capacity_pre dp_l_2 := htable.2.2.2
  have hzeroS : MKZeroPrefixSafety dp_l_2 (capacity_pre+1) := ⟨hz.1,hz.2.1⟩
  have hzeroM : MKZeroPrefixSemantics dp_l_2 (capacity_pre+1) := hz.2.2
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  split_pure_spatial
  · rw [he]
    simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.seg_to_full dp_pre 0 (capacity_pre+1) dp_l_2
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4 := by
  unfold multipleKnapsack_entail_wit_4
  right
  intro capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_4_split_goal_1 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | exact (proof_of_multipleKnapsack_entail_wit_4_split_goal_2 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | exact (proof_of_multipleKnapsack_entail_wit_4_split_goal_3 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | exact (proof_of_multipleKnapsack_entail_wit_4_split_goal_4 capacity_pre n_pre qval0 qidx0 old0 counts_l values_l weights_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)

theorem proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5 := by
  unfold multipleKnapsack_entail_wit_5
  right
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_5_split_goal_1 capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
      | exact (proof_of_multipleKnapsack_entail_wit_5_split_goal_2 capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
      | exact (proof_of_multipleKnapsack_entail_wit_5_split_goal_3 capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6 := by
  unfold multipleKnapsack_entail_wit_6
  right
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_6_split_goal_1 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_6_split_goal_2 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_6_split_goal_3 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7 := by
  unfold multipleKnapsack_entail_wit_7
  right
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_7_split_goal_1 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_7_split_goal_2 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_7_split_goal_3 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_7_split_goal_4 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_7_split_goal_5 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_7_split_goal_6 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
      | exact (proof_of_multipleKnapsack_entail_wit_7_split_goal_7 capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8 := by
  unfold multipleKnapsack_entail_wit_8
  right
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_8_split_goal_1 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31)
      | exact (proof_of_multipleKnapsack_entail_wit_8_split_goal_2 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31)
      | exact (proof_of_multipleKnapsack_entail_wit_8_split_goal_3 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31)

theorem proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9 := by
  unfold multipleKnapsack_entail_wit_9
  right
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_9_split_goal_1 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
      | exact (proof_of_multipleKnapsack_entail_wit_9_split_goal_2 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
      | exact (proof_of_multipleKnapsack_entail_wit_9_split_goal_3 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
      | exact (proof_of_multipleKnapsack_entail_wit_9_split_goal_4 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
      | exact (proof_of_multipleKnapsack_entail_wit_9_split_goal_5 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)

theorem proof_of_multipleKnapsack_entail_wit_10 : multipleKnapsack_entail_wit_10 := by
  unfold multipleKnapsack_entail_wit_10
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_10_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_10_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_10_split_goal_3 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_10_split_goal_4 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_10_split_goal_5 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_10_split_goal_6 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_10_split_goal_7 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)

theorem proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11 := by
  unfold multipleKnapsack_entail_wit_11
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_11_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_11_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)

theorem proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1 := by
  unfold multipleKnapsack_entail_wit_12_1
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_12_1_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49)
      | exact (proof_of_multipleKnapsack_entail_wit_12_1_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49)

theorem proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2 := by
  unfold multipleKnapsack_entail_wit_12_2
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_12_2_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_12_2_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)

theorem proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13 := by
  unfold multipleKnapsack_entail_wit_13
  right
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_13_split_goal_1 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49)
      | exact (proof_of_multipleKnapsack_entail_wit_13_split_goal_2 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49)

theorem proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14 := by
  unfold multipleKnapsack_entail_wit_14
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_14_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_14_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)

theorem proof_of_multipleKnapsack_entail_wit_15_1 : multipleKnapsack_entail_wit_15_1 := by
  unfold multipleKnapsack_entail_wit_15_1
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_3 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_4 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_5 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_6 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_7 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_8 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)
      | exact (proof_of_multipleKnapsack_entail_wit_15_1_split_goal_9 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50)

theorem proof_of_multipleKnapsack_entail_wit_15_2 : multipleKnapsack_entail_wit_15_2 := by
  unfold multipleKnapsack_entail_wit_15_2
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_3 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_4 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_5 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_6 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_7 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_8 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)
      | exact (proof_of_multipleKnapsack_entail_wit_15_2_split_goal_9 capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51)

theorem proof_of_multipleKnapsack_entail_wit_16 : multipleKnapsack_entail_wit_16 := by
  unfold multipleKnapsack_entail_wit_16
  right
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_16_split_goal_1 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52)
      | exact (proof_of_multipleKnapsack_entail_wit_16_split_goal_2 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52)
      | exact (proof_of_multipleKnapsack_entail_wit_16_split_goal_3 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52)
      | exact (proof_of_multipleKnapsack_entail_wit_16_split_goal_4 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52)
      | exact (proof_of_multipleKnapsack_entail_wit_16_split_goal_5 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52)
      | exact (proof_of_multipleKnapsack_entail_wit_16_split_goal_6 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52)
      | exact (proof_of_multipleKnapsack_entail_wit_16_split_goal_7 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt pos k current head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52)

theorem proof_of_multipleKnapsack_entail_wit_17 : multipleKnapsack_entail_wit_17 := by
  unfold multipleKnapsack_entail_wit_17
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_17_split_goal_1 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_17_split_goal_2 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
      | exact (proof_of_multipleKnapsack_entail_wit_17_split_goal_3 capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)

theorem proof_of_multipleKnapsack_entail_wit_18 : multipleKnapsack_entail_wit_18 := by
  unfold multipleKnapsack_entail_wit_18
  right
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt k head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_18_split_goal_1 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i r w v cnt k head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38)

theorem proof_of_multipleKnapsack_entail_wit_19 : multipleKnapsack_entail_wit_19 := by
  unfold multipleKnapsack_entail_wit_19
  right
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_19_split_goal_1 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33)
      | exact (proof_of_multipleKnapsack_entail_wit_19_split_goal_2 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33)
      | exact (proof_of_multipleKnapsack_entail_wit_19_split_goal_3 capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33)

theorem proof_of_multipleKnapsack_entail_wit_20 : multipleKnapsack_entail_wit_20 := by
  unfold multipleKnapsack_entail_wit_20
  right
  intro capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_20_split_goal_1 capacity_pre n_pre counts_l values_l weights_l dp_l_2 old_l_2 qidx_l_2 qval_l_2 i w v cnt PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)

theorem proof_of_multipleKnapsack_entail_wit_21 : multipleKnapsack_entail_wit_21 := by
  unfold multipleKnapsack_entail_wit_21
  right
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_multipleKnapsack_entail_wit_21_split_goal_1 capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
      | exact (proof_of_multipleKnapsack_entail_wit_21_split_goal_2 capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
      | exact (proof_of_multipleKnapsack_entail_wit_21_split_goal_3 capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)


end SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_proof_manual
