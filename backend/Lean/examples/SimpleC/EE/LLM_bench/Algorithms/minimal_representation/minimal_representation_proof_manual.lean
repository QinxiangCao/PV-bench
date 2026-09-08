import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_goal
import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open minimal_representation_goal minimal_representation_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Preserve the source SL tactics and generated residual VCs. The current
-- Goal_apply needs explicit arguments; pure propositions additionally require
-- dump_spatial_left, while spatial split lemmas retain their heap assertions.
theorem proof_of_minimal_representation_entail_wit_1_split_goal_1 : minimal_representation_entail_wit_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_1_split_goal_1
  intro b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dump_pre_spatial
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_1_split_goal_spatial : minimal_representation_entail_wit_1_split_goal_spatial := by
  unfold minimal_representation_entail_wit_1_split_goal_spatial
  intro b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  change _ |-- naive_C_Rules.IntArray.undef_seg b_pre 0 n_pre **
    naive_C_Rules.IntArray.seg b_pre n_pre (n_pre+0) ([] : List Int) **
    naive_C_Rules.IntArray.undef_seg b_pre (n_pre+0) (2*n_pre)
  simp only [Int.add_zero]
  sep_apply_l_atomic (naive_C_Rules.IntArray.undef_full_split_to_undef_seg b_pre n_pre (2*n_pre) (by omega))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.seg_empty b_pre n_pre n_pre)).2)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    rfl

theorem proof_of_minimal_representation_entail_wit_1 : minimal_representation_entail_wit_1 := by
  unfold minimal_representation_entail_wit_1
  right
  intro b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_1_split_goal_1 b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_1_split_goal_spatial b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
    | exact (proof_of_minimal_representation_entail_wit_1_split_goal_1 b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_minimal_representation_entail_wit_1_split_goal_spatial b_pre n_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_minimal_representation_entail_wit_2_split_goal_1 : minimal_representation_entail_wit_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_2_split_goal_1
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  rw [sublist_split 0 (p+1) p l (by omega) (by omega), sublist_single 0 p l (by omega)]

theorem proof_of_minimal_representation_entail_wit_2_split_goal_spatial : minimal_representation_entail_wit_2_split_goal_spatial := by
  unfold minimal_representation_entail_wit_2_split_goal_spatial
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [sublist_split 0 (p+1) p l (by omega) (by omega), sublist_single 0 p l (by omega)]
  rw [show n_pre+(p+1) = n_pre+p+1 by omega]
  cancel

theorem proof_of_minimal_representation_entail_wit_2 : minimal_representation_entail_wit_2 := by
  unfold minimal_representation_entail_wit_2
  right
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_2_split_goal_1 b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_2_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_minimal_representation_entail_wit_2_split_goal_1 b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_minimal_representation_entail_wit_2_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_minimal_representation_entail_wit_3_split_goal_spatial : minimal_representation_entail_wit_3_split_goal_spatial := by
  unfold minimal_representation_entail_wit_3_split_goal_spatial
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hp : p = n_pre := by omega
  rw [hp, sublist_self l n_pre PreH4.symm, show n_pre+n_pre = 2*n_pre by omega]
  sep_apply_l_atomic (naive_C_Rules.IntArray.seg_merge_to_full b_pre 0 n_pre (2*n_pre) l l (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_minimal_representation_entail_wit_3 : minimal_representation_entail_wit_3 := by
  unfold minimal_representation_entail_wit_3
  right
  intro b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_3_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_minimal_representation_entail_wit_3_split_goal_spatial b_pre n_pre best l p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_minimal_representation_entail_wit_4 : minimal_representation_entail_wit_4 := by
  unfold minimal_representation_entail_wit_4
  intro out_pre b_pre n_pre a_pre best l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have Hstate := MRCandidateState_initial__candidate_boundaries l best (by omega) PreH6
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega

theorem proof_of_minimal_representation_entail_wit_5_1_split_goal_1 : minimal_representation_entail_wit_5_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_5_1_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  omega

theorem proof_of_minimal_representation_entail_wit_5_1 : minimal_representation_entail_wit_5_1 := by
  unfold minimal_representation_entail_wit_5_1
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_5_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_5_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_5_2_split_goal_1 : minimal_representation_entail_wit_5_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_5_2_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  omega

theorem proof_of_minimal_representation_entail_wit_5_2 : minimal_representation_entail_wit_5_2 := by
  unfold minimal_representation_entail_wit_5_2
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_5_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_5_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_6_split_goal_1 : minimal_representation_entail_wit_6_split_goal_1 := by
  unfold minimal_representation_entail_wit_6_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro offset ho
  by_cases hk : offset < k
  · exact PreH17 offset (by omega)
  · have heq : offset = k := by omega
    subst offset
    exact PreH1

theorem proof_of_minimal_representation_entail_wit_6 : minimal_representation_entail_wit_6 := by
  unfold minimal_representation_entail_wit_6
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_6_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_6_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_7_1 : minimal_representation_entail_wit_7_1 := by
  unfold minimal_representation_entail_wit_7_1
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best (i+k+2) j := by
    have ht := MRCandidateState_advance_left__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.1 (by omega)
  Right
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_7_2 : minimal_representation_entail_wit_7_2 := by
  unfold minimal_representation_entail_wit_7_2
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best (i+k+1) j := by
    have ht := MRCandidateState_advance_left__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.2 (by omega)
  Right
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_7_3 : minimal_representation_entail_wit_7_3 := by
  unfold minimal_representation_entail_wit_7_3
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best i (j+k+2) := by
    have ht := MRCandidateState_advance_right__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.1 (by omega)
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_7_4 : minimal_representation_entail_wit_7_4 := by
  unfold minimal_representation_entail_wit_7_4
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have Hstate : MRCandidateState l best i (j+k+1) := by
    have ht := MRCandidateState_advance_right__candidate_transitions l best i j k PreH18
      (by constructor <;> omega) (by constructor <;> omega) (by omega) PreH20
      (by unfold MRRotationValue; omega) PreH19
    exact ht.2 (by omega)
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | trivial
      | omega
      | (simpa only [Int.add_assoc] using Hstate)

theorem proof_of_minimal_representation_entail_wit_8_1_split_goal_1 : minimal_representation_entail_wit_8_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_1_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro h
  rcases PreH16 with hb | hb | ⟨hf, _⟩ <;> omega

theorem proof_of_minimal_representation_entail_wit_8_1 : minimal_representation_entail_wit_8_1 := by
  unfold minimal_representation_entail_wit_8_1
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_entail_wit_8_1_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_minimal_representation_entail_wit_8_2_split_goal_1 : minimal_representation_entail_wit_8_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_8_2_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro h
  rcases PreH17 with hb | hb | ⟨hf, _⟩ <;> omega

theorem proof_of_minimal_representation_entail_wit_8_2 : minimal_representation_entail_wit_8_2 := by
  unfold minimal_representation_entail_wit_8_2
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_8_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_8_2_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_8_3 : minimal_representation_entail_wit_8_3 := by
  unfold minimal_representation_entail_wit_8_3
  intro out_pre b_pre n_pre a_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hi : MRValidStart l i := by constructor <;> omega
  have hj : MRValidStart l j := by constructor <;> omega
  have heq : MRRotationEq l i j := by
    unfold MRRotationEq
    rw [PreH5, ← PreH1]
    exact PreH17
  obtain ⟨hlt, hge⟩ := MRCandidateState_equal_exit__candidate_boundaries l best i j hi hj PreH12 PreH15 PreH16 heq
  Left
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega

theorem proof_of_minimal_representation_entail_wit_9_1_split_goal_1 : minimal_representation_entail_wit_9_1_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_1_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_1 : minimal_representation_entail_wit_9_1 := by
  unfold minimal_representation_entail_wit_9_1
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_1_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_1_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_9_2_split_goal_1 : minimal_representation_entail_wit_9_2_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_2_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_2 : minimal_representation_entail_wit_9_2 := by
  unfold minimal_representation_entail_wit_9_2
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_2_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_2_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_9_3_split_goal_1 : minimal_representation_entail_wit_9_3_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_3_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_3 : minimal_representation_entail_wit_9_3 := by
  unfold minimal_representation_entail_wit_9_3
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_3_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_3_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_9_4_split_goal_1 : minimal_representation_entail_wit_9_4_split_goal_1 := by
  unfold minimal_representation_entail_wit_9_4_split_goal_1
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp [sublist]

theorem proof_of_minimal_representation_entail_wit_9_4 : minimal_representation_entail_wit_9_4 := by
  unfold minimal_representation_entail_wit_9_4
  right
  intro n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_9_4_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_minimal_representation_entail_wit_9_4_split_goal_1 n_pre best l i j k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_minimal_representation_entail_wit_10_split_goal_1 : minimal_representation_entail_wit_10_split_goal_1 := by
  unfold minimal_representation_entail_wit_10_split_goal_1
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hs : MRValidStart l best := by constructor <;> omega
  have hn := MRRotation_Zlength__output_finalization l best hs
  rw [← MRRotation_Znth__output_finalization l best k hs (by omega),
    sublist_split 0 (k+1) k (MRRotation l best) (by omega) (by omega),
    sublist_single 0 k (MRRotation l best) (by omega)]

theorem proof_of_minimal_representation_entail_wit_10 : minimal_representation_entail_wit_10 := by
  unfold minimal_representation_entail_wit_10
  right
  intro n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_entail_wit_10_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_entail_wit_10_split_goal_1 n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_minimal_representation_return_wit_1_split_goal_spatial : minimal_representation_return_wit_1_split_goal_spatial := by
  unfold minimal_representation_return_wit_1_split_goal_spatial
  intro out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hs : MRValidStart l best := by constructor <;> omega
  have hn := MRRotation_Zlength__output_finalization l best hs
  have hk : k = n_pre := by omega
  rw [hk, sublist_self (MRRotation l best) n_pre (by omega)]
  sep_apply_l_atomic (naive_C_Rules.IntArray.seg_to_full out_pre 0 n_pre (MRRotation l best))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_minimal_representation_return_wit_1 : minimal_representation_return_wit_1 := by
  unfold minimal_representation_return_wit_1
  right
  intro out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_minimal_representation_return_wit_1_split_goal_spatial out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_minimal_representation_return_wit_1_split_goal_spatial out_pre n_pre best l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

end SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_proof_manual
