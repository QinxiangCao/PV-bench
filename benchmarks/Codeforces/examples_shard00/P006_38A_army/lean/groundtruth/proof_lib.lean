import Codeforces.examples_shard00.P006_38A_army.lean.spec_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard00.P006_38A_army.lean.groundtruth.proof_lib

open Codeforces.examples_shard00.P006_38A_army.lean
open scoped SimpleC

open AUXLib

theorem Spec_succ__loop_step (n : Int) (years : List Int) (a i ans : Int)
    (ha : 1 ≤ a) (hai : a ≤ i) (hi : i ≤ Zlength years)
    (hs : Spec n years a i ans) :
    Spec n years a (i + 1) (ans + Znth i (0 :: years) 0) := by
  change ans = sum (sublist (a - 1) (i - 1) years) at hs
  change ans + Znth i (0 :: years) 0 = sum (sublist (a - 1) (i + 1 - 1) years)
  rw [show i + 1 - 1 = i by omega,
    sublist_split (a - 1) i (i - 1) years (by omega) (by omega), sum_app]
  have hsingle := sublist_single 0 (i - 1) years (by omega)
  rw [show i - 1 + 1 = i by omega] at hsingle
  rw [hsingle, Znth_cons 0 i 0 years (by omega)]
  change ans + Znth (i - 1) years 0 = sum (sublist (a - 1) (i - 1) years) + (Znth (i - 1) years 0 + 0)
  omega

end Codeforces.examples_shard00.P006_38A_army.lean.groundtruth.proof_lib
