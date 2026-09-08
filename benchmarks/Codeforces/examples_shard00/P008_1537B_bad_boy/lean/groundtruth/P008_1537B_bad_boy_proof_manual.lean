import Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.P008_1537B_bad_boy_goal
import Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.P008_1537B_bad_boy_proof_auto
import Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.proof_lib

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.P008_1537B_bad_boy_proof_manual

open Codeforces.examples_shard00.P008_1537B_bad_boy.lean
open Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.proof_lib
open Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.P008_1537B_bad_boy_goal
open scoped SimpleC

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.P008_1537B_bad_boy_goal
open Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.proof_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro out j i m n start _ _ _ _ _ _ hn hnmax hm hmmax hi hj hilo hihi hjlo hjhi
  have hs : InRoom n m start := by
    dsimp [InRoom, fst, snd] at *
    omega
  have hspec := opposite_corners_spec__final_result n m start hn hm hs
  Exists ((1, 1) : Int × Int) ((n, m) : Int × Int)
  simp only [fst, snd]
  split_pure_spatial
  · rel_rw [naive_C_Rules.Int64Array.full_unfold out 4 ([1, n, m] : List Int) (1 : Int),
      naive_C_Rules.Int64Array.seg_unfold out 1 4 ([n, m] : List Int) (1 : Int),
      naive_C_Rules.Int64Array.seg_unfold out (1 + 1) 4 [m] n,
      naive_C_Rules.Int64Array.seg_unfold out ((1 + 1) + 1) 4 [] m]
    simp only [Int.reduceAdd]
    rel_rw [
      naive_C_Rules.Int64Array.seg_empty out 4]
    entailer!
  · dump_pre_spatial
    exact hspec

end Codeforces.examples_shard00.P008_1537B_bad_boy.lean.groundtruth.P008_1537B_bad_boy_proof_manual
