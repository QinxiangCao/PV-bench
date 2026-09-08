import Algorithms.minimal_representation.lean.spec_lib

namespace Algorithms.minimal_representation.lean

open AUXLib

def MRCandidateState (l : List Int) (best i j : Int) : Prop :=
  best = i ∨ best = j ∨ (max i j ≤ best ∧ ¬ MRRotationEq l i j)

end Algorithms.minimal_representation.lean
