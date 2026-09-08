import Algorithms.modular_inverse.lean.groundtruth.modular_inverse_goal
import Algorithms.modular_inverse.lean.groundtruth.modular_inverse_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.modular_inverse.lean.groundtruth.modular_inverse_proof_manual

open Algorithms.modular_inverse.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

end ProofSupport

open ProofSupport
open Algorithms.modular_inverse.lean.groundtruth.modular_inverse_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.modular_inverse.lean.groundtruth.modular_inverse_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1 := by
  pre_process
  Exists (a_pre * Z.quot x_callee_v modulus_pre + y_callee_v - a_pre)
  have hr := rem_bounds x_callee_v modulus_pre (by omega)
  have hq := Z.quot_rem x_callee_v modulus_pre (by omega)
  entailer!
  all_goals grind

theorem proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2 := by
  pre_process
  Exists (a_pre * Z.quot x_callee_v modulus_pre + y_callee_v)
  have hr := rem_bounds x_callee_v modulus_pre (by omega)
  have hq := Z.quot_rem x_callee_v modulus_pre (by omega)
  entailer!
  all_goals grind

end Algorithms.modular_inverse.lean.groundtruth.modular_inverse_proof_manual
