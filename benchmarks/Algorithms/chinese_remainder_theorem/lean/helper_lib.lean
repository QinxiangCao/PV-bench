import Algorithms.chinese_remainder_theorem.lean.spec_lib

namespace Algorithms.chinese_remainder_theorem.lean

open AUXLib

def CRTProcessedCongruences (remainders moduli : List Int) (processed result : Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < processed) → Z.modulo result (Znth i moduli 0) = Znth i remainders 0

end Algorithms.chinese_remainder_theorem.lean
