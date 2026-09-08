import Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.P014_1765E_exchange_goal
import Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.P014_1765E_exchange_proof_auto
import Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.proof_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.P014_1765E_exchange_proof_manual

open Codeforces.examples_shard01.P014_1765E_exchange.lean
open Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.proof_lib
open Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.P014_1765E_exchange_goal
open scoped SimpleC

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.P014_1765E_exchange_goal Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.proof_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro b a n h1 h2 h3 h4 h5 h6 h7
  have he : Z.quot ((n+a)-1) a = Z.div ((n+a)-1) a := by
    unfold Z.quot Z.div
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  rw [he]
  exact exchange_nonprofitable_spec__exchange_minimum n a b h2 h4 h1

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro b a n h1 h2 h3 h4 h5 h6 h7
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 b a n h1 h2 h3 h4 h5 h6 h7

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro b a n h1 h2 h3 h4 h5 h6 h7
  exact exchange_profitable_spec__exchange_minimum n a b h1 h6 h2

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro b a n h1 h2 h3 h4 h5 h6 h7
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_2_split_goal_1 b a n h1 h2 h3 h4 h5 h6 h7

end Codeforces.examples_shard01.P014_1765E_exchange.lean.groundtruth.P014_1765E_exchange_proof_manual
