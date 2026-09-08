import Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.P012_1326A_bad_ugly_numbers_goal
import Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.P012_1326A_bad_ugly_numbers_proof_auto
import Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.proof_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.P012_1326A_bad_ugly_numbers_proof_manual

open Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean
open Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.proof_lib
open Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.P012_1326A_bad_ugly_numbers_goal
open scoped SimpleC

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.P012_1326A_bad_ugly_numbers_goal Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.proof_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro out_pre n_pre PreH1 PreH2 PreH3
  Exists [50]
  have hs : (((out_pre+0*sizeof(CHAR)) # Char |-> (50 : Int)) |-- charArray.seg out_pre 0 1 [(50 : Int)]) := charArray.seg_single out_pre 0 (50 : Int)
  sep_apply hs
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | omega | rfl | intro k hk; omega

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro n_pre chars_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  cases chars_2 with
  | nil => change 0=i at PreH6;omega
  | cons x xs => exact PreH7

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro n_pre chars_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  right
  intro n_pre chars_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 n_pre chars_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_solver_entail_wit_2_split_goal_2 n_pre chars_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  left
  intro out_pre n_pre chars_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : i_2=n_pre := by omega
  have hbad : BadUglyDigits n_pre (chars_2.map (fun c => c-48)) := by
    apply two_then_threes_bad_ugly__spec_results n_pre _ PreH2
    · rw [Zlength_map_Z__spec_results];omega
    · rw [Znth_map_inbounds_Z__spec_results _ chars_2 0 0 0 (by omega)]
      omega
    · intro k hk
      rw [Znth_map_inbounds_Z__spec_results _ chars_2 k 0 0 (by omega)]
      have hh := PreH8 k (by omega)
      omega
  have hspec : Spec n_pre (Some (chars_2.map (fun c => c-48))) := Or.inl ⟨_,rfl,hbad⟩
  refine Automation.exp_right_rule (CRules := SacContext.rules) chars_2 ?_
  refine Automation.exp_right_rule (CRules := SacContext.rules) (chars_2.map (fun c => c-48)) ?_
  sep_apply (charArray.seg_to_full out_pre 0 (i_2+1) (chars_2++[0]))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  split_pure_spatial
  · rw [PreH6];cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve
      | exact hspec
      | simp only [Zlength_map_Z__spec_results]
      | rw [Zlength_map_Z__spec_results];omega
      | intro j hj
        rw [Zlength_map_Z__spec_results] at hj
        rw [Znth_map_inbounds_Z__spec_results _ chars_2 j 0 0 hj]
        omega

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  intro out_pre n_pre PreH1 PreH2 PreH3
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · rfl
    · refine Or.inr ⟨rfl,?_⟩
      rw [PreH1]
      exact no_bad_ugly_length_one__spec_results

end Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean.groundtruth.P012_1326A_bad_ugly_numbers_proof_manual
