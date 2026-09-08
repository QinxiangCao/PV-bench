import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_goal
import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open extended_chinese_remainder_theorem_goal extended_chinese_remainder_theorem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Use the original generated residual branch and SL preprocessing. Goal_apply
-- requires explicit arguments in Lean; pure split results also need the
-- dump_spatial_left bridge from entailments to propositions.

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_safety_wit_7_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH1 ⟨PreH4, PreH6⟩
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_safety_wit_7_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH1 ⟨PreH4, PreH6⟩
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7 := by
  unfold extended_chinese_remainder_theorem_safety_wit_7
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_safety_wit_10_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_safety_wit_10_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_10 : extended_chinese_remainder_theorem_safety_wit_10 := by
  unfold extended_chinese_remainder_theorem_safety_wit_10
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_safety_wit_11_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_safety_wit_11_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := bounded_merge_arithmetic__machine_bounds answer lcm x reduced_modulus ⟨PreH6, PreH7⟩ ⟨PreH16, PreH17⟩ PreH8 PreH19
  omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_11 : extended_chinese_remainder_theorem_safety_wit_11 := by
  unfold extended_chinese_remainder_theorem_safety_wit_11
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_1_split_goal_1
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH1.1

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_1
  right
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_1
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  exact crt_prefix_meaning_one__prefix_boundaries residue_values modulus_values n_pre PreH2 PreH1

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_2
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_3
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_4
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_split_goal_5
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre 0 PreH2 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2 : extended_chinese_remainder_theorem_entail_wit_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2
  right
  intro n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 n_pre modulus_values residue_values PreH1 PreH2 PreH3 PreH4)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hs := bezout_coefficient_strict__gcd_branch_setup lcm (Znth i modulus_values 0) retval x_callee_v y_callee_v hb.1.1 PreH2 PreH1 PreH5 PreH3 PreH4
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hs := bezout_coefficient_strict__gcd_branch_setup lcm (Znth i modulus_values 0) retval x_callee_v y_callee_v hb.1.1 PreH2 PreH1 PreH5 PreH3 PreH4
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hs := PreH9.2 i (by omega)
  have hp := PreH16.1
  change retval = Z.gcd lcm (Znth i modulus_values 0) at PreH2
  rw [← hp, ← PreH2] at hs
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH7 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH3

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH2

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1
  right
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hd := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval (by omega) (by omega) PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hs := PreH10.2 i (by omega)
  have hp := PreH17.1
  change retval = Z.gcd lcm (Znth i modulus_values 0) at PreH2
  rw [← hp, ← PreH2] at hs
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH8 (by omega)
  have hq := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 PreH2 PreH1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  simpa only [PreH6] using PreH3

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try simp only [INT_MAX, INT_MIN] at *
  exact PreH2

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2
  right
  intro n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 n_pre modulus_values residue_values lcm answer i y_callee_v x_callee_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hd : Z.divide gcd (Znth i residue_values 0-answer) := by
    rw [PreH14]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm PreH4 PreH13 ⟨PreH6, PreH8⟩
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) gcd PreH15 hd
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm
  obtain ⟨hb, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have hr : reduced_modulus = Z.div (Znth i modulus_values 0) gcd := PreH17.trans hmod
  apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) gcd x y (retval+reduced_modulus) (q-1) PreH14 PreH15 hd PreH16
  rw [← hr]
  grind

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hr := PreH17.trans (quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm)
  have hp := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm gcd reduced_modulus PreH3 ⟨PreH6, PreH8⟩ PreH11 PreH13 PreH14 PreH15 hr
  have hs := (PreH5.1 (i+1) (by omega)).2
  rw [hp] at hs
  exact hs

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hb := PreH2.1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  exact replace_Znth_Znth i residue_values 0

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_1 : extended_chinese_remainder_theorem_entail_wit_4_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_1
  right
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hd : Z.divide gcd (Znth i residue_values 0-answer) := by
    rw [PreH14]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm PreH4 PreH13 ⟨PreH6, PreH8⟩
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) gcd PreH15 hd
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm
  obtain ⟨hb, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have hr : reduced_modulus = Z.div (Znth i modulus_values 0) gcd := PreH17.trans hmod
  apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) gcd x y retval q PreH14 PreH15 hd PreH16
  rw [← hr]
  grind

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH14]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hr := PreH17.trans (quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH15 hm)
  have hp := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm gcd reduced_modulus PreH3 ⟨PreH6, PreH8⟩ PreH11 PreH13 PreH14 PreH15 hr
  have hs := (PreH5.1 (i+1) (by omega)).2
  rw [hp] at hs
  exact hs

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  have hb := PreH2.1
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  try simp only [INT_MAX, INT_MIN] at *
  exact replace_Znth_Znth i residue_values 0

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_4_2 : extended_chinese_remainder_theorem_entail_wit_4_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_4_2
  right
  intro n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 n_pre modulus_values residue_values i answer lcm gcd x y reduced_modulus retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_5_split_goal_1
  intro n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  have hm : Z.divide gcd (Znth i modulus_values 0) := by
    rw [PreH11]
    exact Z.gcd_divide_r lcm (Znth i modulus_values 0)
  have hr := PreH13.trans (quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) gcd PreH12 hm)
  exact crt_prefix_meaning_merge__merge_transition residue_values modulus_values n_pre i answer lcm gcd reduced_modulus x PreH1 PreH2 (by omega) PreH8 PreH10 PreH11 PreH12 hr ⟨PreH16, PreH17⟩ PreH20

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_5_split_goal_2
  intro n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  try simp only [INT_MAX, INT_MIN] at *
  have hu := Int.mul_le_mul_of_nonneg_right (show x+1 ≤ reduced_modulus by omega) (Int.le_of_lt PreH8)
  simp only [Int.add_mul, Int.one_mul] at hu
  rw [Int.mul_comm reduced_modulus lcm] at hu
  omega

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_5 : extended_chinese_remainder_theorem_entail_wit_5 := by
  unfold extended_chinese_remainder_theorem_entail_wit_5
  right
  intro n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 n_pre modulus_values residue_values i answer lcm gcd reduced_modulus x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1 : extended_chinese_remainder_theorem_return_wit_1_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_return_wit_1_split_goal_1
  intro n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  try simp only [INT_MAX, INT_MIN] at *
  exact crt_prefix_meaning_to_result__prefix_boundaries residue_values modulus_values n_pre i answer lcm (by omega) ⟨PreH7, PreH8⟩ PreH11

theorem proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1 := by
  unfold extended_chinese_remainder_theorem_return_wit_1
  right
  intro n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1 n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | exact (proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1 n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | trivial

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH9 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try simp only [INT_MAX, INT_MIN] at *
  dump_pre_spatial
  have hb := extended_crt_index_bounds__machine_bounds residue_values modulus_values n_pre i PreH9 (by omega)
  omega

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_4_pure
  right
  intro combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | Goal_apply (proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 combined_modulus_pre moduli_pre residues_pre n_pre modulus_values residue_values lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_proof_manual
