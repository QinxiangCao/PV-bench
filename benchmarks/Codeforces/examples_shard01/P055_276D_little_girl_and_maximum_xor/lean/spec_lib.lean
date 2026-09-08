import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P055_276D_little_girl_and_maximum_xor.lean

open AUXLib

open MaxMinLib

def Pre (l r : Int) : Prop := True

def Spec (l r out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun v => ∃ a b, (l ≤ a ∧ a ≤ b) ∧ b ≤ r ∧ v = Z.lxor a b) (fun x => x) out

end Codeforces.examples_shard01.P055_276D_little_girl_and_maximum_xor.lean
