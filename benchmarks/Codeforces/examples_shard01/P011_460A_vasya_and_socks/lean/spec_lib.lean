import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Codeforces.examples_shard01.P011_460A_vasya_and_socks.lean

def Pre (n m : Int) : Prop := True

def Spec (n m out : Int) : Prop :=
  out > 0 ∧ (∀ d : Int, (1 ≤ d ∧ d ≤ out) → n + Z.div (d - 1) m - (d - 1) > 0) ∧
    n + Z.div out m - out = 0

end Codeforces.examples_shard01.P011_460A_vasya_and_socks.lean
