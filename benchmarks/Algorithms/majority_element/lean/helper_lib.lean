import Algorithms.majority_element.lean.spec_lib

namespace Algorithms.majority_element.lean

open AUXLib

def repeated (candidate vote : Int) : List Int := List.replicate vote.toNat candidate

def MajorityOnReduced (major candidate vote : Int) (rest : List Int) : Prop :=
  0 ≤ vote ∧ IsMajorityElement major (repeated candidate vote ++ rest)

end Algorithms.majority_element.lean
