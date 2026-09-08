import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_goal
import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_proof_auto

import ListLib.General.Length

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open matrix_chain_multiplication_goal matrix_chain_multiplication_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem candidate_upper (dims table : List Int) (n len l k : Int)
    (hn : n ≤ 8) (hlen : 2 ≤ len) (hl : 0 ≤ l) (hfit : l+len ≤ n)
    (hk : l ≤ k ∧ k < l+len-1)
    (hd : MatrixChainDimensionsBounded dims n)
    (hprogress : MatrixChainLengthsDone dims table n len) :
    Znth (l*n+k) table 0 + Znth ((k+1)*n+(l+len-1)) table 0 +
      Znth l dims 0*Znth (k+1) dims 0*Znth ((l+len-1)+1) dims 0 ≤ 7000000 := by
  have hml := hprogress.2 (k-l+1) l k ⟨by omega, by omega⟩ (by omega) hl (by omega)
  have hmr := hprogress.2 (l+len-1-k) (k+1) (l+len-1) ⟨by omega, by omega⟩
    (by omega) (by omega) (by omega)
  have hb1 := matrix_chain_interval_minimum_upper_bound__candidate_progress
    dims n l k _ hd hl hk.1 (by omega) hml
  have hb2 := matrix_chain_interval_minimum_upper_bound__candidate_progress
    dims n (k+1) (l+len-1) _ hd (by omega) (by omega) (by omega) hmr
  have hb3 := matrix_chain_dimensions_product_bound _ _ _
    (hd.2 l ⟨hl, by omega⟩) (hd.2 (k+1) ⟨by omega, by omega⟩)
    (hd.2 ((l+len-1)+1) ⟨by omega, by omega⟩)
  omega

private theorem matrix_index_injective (n i j k l : Int) (hn : 1 ≤ n)
    (hj : 0 ≤ j ∧ j < n) (hl : 0 ≤ l ∧ l < n)
    (he : i*n+j = k*n+l) : i = k ∧ j = l := by
  have hi : i = k := by
    rcases lt_trichotomy i k with h | h | h
    · have hp : (i+1)*n ≤ k*n := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    · exact h
    · have hp : (k+1)*n ≤ i*n := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
  exact ⟨hi, by rw [hi] at he; omega⟩

theorem proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 : matrixChainMinCost_entail_wit_1_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_1_split_goal_1
  intro matrix_count_pre dimensions_l PreH1 PreH2 PreH3 PreH4
  exact ⟨rfl, fun i hi => False.elim (by omega)⟩

theorem proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 : matrixChainMinCost_entail_wit_2_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_2_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  rcases PreH8 with ⟨hlen, hzero⟩
  constructor
  · rw [Zlength_app, Zlength_cons, Zlength_nil, hlen]
    omega
  · intro index hi
    by_cases hlt : index < i
    · have hn : Znth index (cost_l_2 ++ [0]) 0 = Znth index cost_l_2 0 :=
        ListLib.app_Znth1 0 cost_l_2 [0] index ⟨hi.1, by change index < Zlength cost_l_2; omega⟩
      rw [hn]
      exact hzero index ⟨hi.1, hlt⟩
    · have he : index = i := by omega
      subst index
      rw [app_Znth2 0 cost_l_2 [0] i (by omega), hlen, Int.sub_self]
      rfl

theorem proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 : matrixChainMinCost_entail_wit_5_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_5_split_goal_1
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact ⟨PreH10, fun l r hl hr hfit => False.elim (by omega)⟩

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 : matrixChainMinCost_entail_wit_6_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_1
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 : matrixChainMinCost_entail_wit_6_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_2
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_3 : matrixChainMinCost_entail_wit_6_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_3
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 (left+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_4 : matrixChainMinCost_entail_wit_6_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_4
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 (left+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_5 : matrixChainMinCost_entail_wit_6_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_5
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 left ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_6 : matrixChainMinCost_entail_wit_6_split_goal_6 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_6
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact (PreH10.2 left ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_7 : matrixChainMinCost_entail_wit_6_split_goal_7 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_7
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 ((left+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_8 : matrixChainMinCost_entail_wit_6_split_goal_8 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_8
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 ((left+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_9 : matrixChainMinCost_entail_wit_6_split_goal_9 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_9
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 (left*matrix_count_pre+left) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_10 : matrixChainMinCost_entail_wit_6_split_goal_10 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_10
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH11 (left*matrix_count_pre+left) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_11 : matrixChainMinCost_entail_wit_6_split_goal_11 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_11
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre (left+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_6_split_goal_12 : matrixChainMinCost_entail_wit_6_split_goal_12 := by
  unfold matrixChainMinCost_entail_wit_6_split_goal_12
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb := matrix_chain_index_bounds matrix_count_pre left left (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 : matrixChainMinCost_entail_wit_7_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_1
  intro matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact matrix_chain_split_progress_initial__candidate_progress _ _ _ _ _ _ PreH34

theorem proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 : matrixChainMinCost_entail_wit_7_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_7_split_goal_2
  intro matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact candidate_upper dimensions_l cost_l matrix_count_pre chain_length left left
    (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ PreH32 PreH34.1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 : matrixChainMinCost_entail_wit_8_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 : matrixChainMinCost_entail_wit_8_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_2
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 ((left+chain_length-1)+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_3 : matrixChainMinCost_entail_wit_8_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_3
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 (split+1) ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_4 : matrixChainMinCost_entail_wit_8_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_4
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 (split+1) ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_5 : matrixChainMinCost_entail_wit_8_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_5
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 left ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_6 : matrixChainMinCost_entail_wit_8_split_goal_6 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_6
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (PreH17.2 left ⟨by omega, by omega⟩).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_7 : matrixChainMinCost_entail_wit_8_split_goal_7 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_7
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 ((split+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH16]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_8 : matrixChainMinCost_entail_wit_8_split_goal_8 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_8
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 ((split+1)*matrix_count_pre+(left+chain_length-1)) (by rw [PreH16]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_9 : matrixChainMinCost_entail_wit_8_split_goal_9 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_9
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 (left*matrix_count_pre+split) (by rw [PreH16]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_10 : matrixChainMinCost_entail_wit_8_split_goal_10 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_10
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact (PreH18 (left*matrix_count_pre+split) (by rw [PreH16]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_11 : matrixChainMinCost_entail_wit_8_split_goal_11 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_11
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre (split+1) (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_8_split_goal_12 : matrixChainMinCost_entail_wit_8_split_goal_12 := by
  unfold matrixChainMinCost_entail_wit_8_split_goal_12
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hb := matrix_chain_index_bounds matrix_count_pre left split (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact hb.2

theorem proof_of_matrixChainMinCost_entail_wit_9_split_goal_1 : matrixChainMinCost_entail_wit_9_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_9_split_goal_1
  intro matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  rfl

theorem proof_of_matrixChainMinCost_entail_wit_9_split_goal_2 : matrixChainMinCost_entail_wit_9_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_9_split_goal_2
  intro matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  exact candidate_upper dimensions_l cost_l matrix_count_pre chain_length left split
    (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ PreH36 PreH38.1.1

theorem proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1 : matrixChainMinCost_entail_wit_10_1_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_10_1_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [PreH8] at PreH21
  exact matrix_chain_split_progress_better__min_update _ _ _ _ _ _ _ _ _
    (by omega) (by omega) PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1 : matrixChainMinCost_entail_wit_10_2_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_10_2_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [PreH8] at PreH21
  exact matrix_chain_split_progress_not_better__min_update _ _ _ _ _ _ _ _ _
    (by omega) (by omega) PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 : matrixChainMinCost_entail_wit_11_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  apply matrix_chain_split_progress_complete__min_update dimensions_l cost_l_2 matrix_count_pre
    chain_length left (left+chain_length-1) best (by omega) (by omega) rfl (by omega) (by omega)
  convert PreH19 using 1 <;> omega

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 : matrixChainMinCost_entail_wit_11_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_2
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  convert PreH19 using 1 <;> omega

theorem proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 : matrixChainMinCost_entail_wit_11_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_11_split_goal_3
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2

theorem proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 : matrixChainMinCost_entail_wit_12_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_12_split_goal_1
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hcur : 0 ≤ left*matrix_count_pre+(left+chain_length-1) ∧
      left*matrix_count_pre+(left+chain_length-1) < Zlength cost_l_2 := by
    rw [PreH15]
    exact matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have hd := PreH18.1.1
  have hp := PreH18.1.2
  constructor
  · refine ⟨hd.1, ?_⟩
    intro len l r hlen hr hl hfit
    have hidx : 0 ≤ l*matrix_count_pre+r ∧ l*matrix_count_pre+r < Zlength cost_l_2 := by
      rw [PreH15]
      exact matrix_chain_index_bounds matrix_count_pre l r (by omega)
        ⟨hl, by omega⟩ ⟨by omega, by omega⟩
    have hneq : left*matrix_count_pre+(left+chain_length-1) ≠ l*matrix_count_pre+r := by
      intro he
      have hh := matrix_index_injective matrix_count_pre left (left+chain_length-1) l r
        (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
      omega
    rw [Znth_replace_Znth_Diff 0 cost_l_2 _ _ best hcur hidx hneq]
    exact hd.2 len l r hlen hr hl hfit
  · intro l r hl hr hfit
    by_cases he : l = left
    · subst l
      have her : r = left+chain_length-1 := by omega
      subst r
      rw [Znth_replace_Znth_Same 0 cost_l_2 _ best hcur]
      convert PreH19 using 1 <;> omega
    · have hidx : 0 ≤ l*matrix_count_pre+r ∧ l*matrix_count_pre+r < Zlength cost_l_2 := by
        rw [PreH15]
        exact matrix_chain_index_bounds matrix_count_pre l r (by omega)
          ⟨hl.1, by omega⟩ ⟨by omega, by omega⟩
      have hneq : left*matrix_count_pre+(left+chain_length-1) ≠ l*matrix_count_pre+r := by
        intro hi
        have hh := matrix_index_injective matrix_count_pre left (left+chain_length-1) l r
          (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hi
        omega
      rw [Znth_replace_Znth_Diff 0 cost_l_2 _ _ best hcur hidx hneq]
      exact hp l r ⟨hl.1, by omega⟩ hr hfit

theorem proof_of_matrixChainMinCost_entail_wit_12_split_goal_2 : matrixChainMinCost_entail_wit_12_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_12_split_goal_2
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hcur : 0 ≤ left*matrix_count_pre+(left+chain_length-1) ∧
      left*matrix_count_pre+(left+chain_length-1) < Zlength cost_l_2 := by
    rw [PreH15]
    exact matrix_chain_index_bounds matrix_count_pre left (left+chain_length-1) (by omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  intro index hi
  rw [Zlength_replace_Znth] at hi
  by_cases he : left*matrix_count_pre+(left+chain_length-1) = index
  · rw [←he, Znth_replace_Znth_Same 0 cost_l_2 _ best hcur]
    exact ⟨by omega, by omega⟩
  · rw [Znth_replace_Znth_Diff 0 cost_l_2 _ index best hcur hi he]
    exact PreH17 index hi

theorem proof_of_matrixChainMinCost_entail_wit_12_split_goal_3 : matrixChainMinCost_entail_wit_12_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_12_split_goal_3
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  exact PreH15

theorem proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 : matrixChainMinCost_entail_wit_13_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_13_split_goal_1
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  refine ⟨by omega, ?_⟩
  intro len l r hlen hr hl hfit
  by_cases hlt : len < chain_length
  · exact PreH12.1.2 len l r ⟨hlen.1, hlt⟩ hr hl hfit
  · have he : len = chain_length := by omega
    subst len
    exact PreH12.2 l r ⟨hl, by omega⟩ hr hfit

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_1 : matrixChainMinCost_entail_wit_14_split_goal_1 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_1
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine ⟨PreH4, ?_⟩
  simpa only [Int.zero_mul, Int.zero_add] using PreH10.2 matrix_count_pre 0 (matrix_count_pre-1)
    ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_2 : matrixChainMinCost_entail_wit_14_split_goal_2 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_2
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine ⟨PreH5, ?_⟩
  intro l r hr
  exact PreH10.2 (r-l+1) l r ⟨by omega, by omega⟩ (by omega) hr.1 (by omega)

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_3 : matrixChainMinCost_entail_wit_14_split_goal_3 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_3
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  convert PreH10 using 1 <;> omega

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_4 : matrixChainMinCost_entail_wit_14_split_goal_4 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_4
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hb := matrix_chain_index_bounds matrix_count_pre 0 (matrix_count_pre-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  simp only [Int.zero_mul, Int.zero_add] at hb
  exact (PreH9 (matrix_count_pre-1) (by rw [PreH5]; exact hb)).2

theorem proof_of_matrixChainMinCost_entail_wit_14_split_goal_5 : matrixChainMinCost_entail_wit_14_split_goal_5 := by
  unfold matrixChainMinCost_entail_wit_14_split_goal_5
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hb := matrix_chain_index_bounds matrix_count_pre 0 (matrix_count_pre-1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  simp only [Int.zero_mul, Int.zero_add] at hb
  exact (PreH9 (matrix_count_pre-1) (by rw [PreH5]; exact hb)).1

theorem proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1 := by
  unfold matrixChainMinCost_entail_wit_1
  right
  intro matrix_count_pre dimensions_l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 matrix_count_pre dimensions_l PreH1 PreH2 PreH3 PreH4

theorem proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2 := by
  unfold matrixChainMinCost_entail_wit_2
  right
  intro matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

theorem proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3 := by
  unfold matrixChainMinCost_entail_wit_3
  right
  intro cost_pre matrix_count_pre dimensions_l cost_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : i = matrix_count_pre*matrix_count_pre := by omega
  subst i
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cost_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using
      intArray.seg_to_full cost_pre 0 (matrix_count_pre*matrix_count_pre) cost_l_2
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | exact PreH8.1
    · exact matrix_chain_zero_table_lengths_done__initialization _ _ _ PreH2 PreH4 PreH8
    · intro index hi
      rw [PreH8.2 index (by rw [←PreH8.1]; exact hi)]
      omega

theorem proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5 := by
  unfold matrixChainMinCost_entail_wit_5
  right
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6 := by
  unfold matrixChainMinCost_entail_wit_6
  right
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_3 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_4 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_5 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_6 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_7 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_8 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_9 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_10 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_11 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_matrixChainMinCost_entail_wit_6_split_goal_12 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7 := by
  unfold matrixChainMinCost_entail_wit_7
  right
  intro matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
      | exact proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 matrix_count_pre dimensions_l cost_l chain_length left right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34

theorem proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8 := by
  unfold matrixChainMinCost_entail_wit_8
  right
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_3 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_4 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_5 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_6 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_7 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_8 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_9 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_10 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_11 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_8_split_goal_12 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_matrixChainMinCost_entail_wit_9 : matrixChainMinCost_entail_wit_9 := by
  unfold matrixChainMinCost_entail_wit_9
  right
  intro matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_9_split_goal_1 matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
      | exact proof_of_matrixChainMinCost_entail_wit_9_split_goal_2 matrix_count_pre dimensions_l cost_l chain_length left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38

theorem proof_of_matrixChainMinCost_entail_wit_10_1 : matrixChainMinCost_entail_wit_10_1 := by
  unfold matrixChainMinCost_entail_wit_10_1
  right
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_10_2 : matrixChainMinCost_entail_wit_10_2 := by
  unfold matrixChainMinCost_entail_wit_10_2
  right
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11 := by
  unfold matrixChainMinCost_entail_wit_11
  right
  intro matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12 := by
  unfold matrixChainMinCost_entail_wit_12
  right
  intro matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_12_split_goal_2 matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_matrixChainMinCost_entail_wit_12_split_goal_3 matrix_count_pre dimensions_l cost_l_2 chain_length left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13 := by
  unfold matrixChainMinCost_entail_wit_13
  right
  intro matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 matrix_count_pre dimensions_l left chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_matrixChainMinCost_entail_wit_14 : matrixChainMinCost_entail_wit_14 := by
  unfold matrixChainMinCost_entail_wit_14
  right
  intro matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_1 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_2 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_3 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_4 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_matrixChainMinCost_entail_wit_14_split_goal_5 matrix_count_pre dimensions_l chain_length cost_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_proof_manual
