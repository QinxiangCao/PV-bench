import Algorithms.integer_divide.lean.spec_lib

namespace Algorithms.integer_divide.lean

open AUXLib

def FactorizationProgress (original : Int) (factors : List Int)
    (remaining candidate : Int) : Prop :=
  factors.foldr (· * ·) 1 * remaining = original ∧
  Forall prime factors ∧ Sorted (· ≤ ·) factors ∧
  Forall (fun factor => factor ≤ candidate) factors ∧
  ∀ d : Int, 2 ≤ d ∧ d < candidate → ¬ Z.divide d remaining

end Algorithms.integer_divide.lean
