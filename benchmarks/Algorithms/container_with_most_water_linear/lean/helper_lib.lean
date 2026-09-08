import Algorithms.container_with_most_water_linear.lean.spec_lib

namespace Algorithms.container_with_most_water_linear.lean

open AUXLib

def LinearContainerBest (l : List Int) (best : Int) : Prop :=
  best = 0 ∨ ∃ i j, LinearContainerPair l i j ∧ best = LinearContainerArea l i j

def LinearContainerRemaining (l : List Int) (left right i j : Int) : Prop :=
  LinearContainerPair l i j ∧ left ≤ i ∧ j ≤ right

def LinearContainerTwoPointerInvariant (l : List Int) (left right best : Int) : Prop :=
  LinearContainerBest l best ∧ ∀ i j, LinearContainerPair l i j →
    LinearContainerArea l i j ≤ best ∨ ∃ p q, LinearContainerRemaining l left right p q ∧
      LinearContainerArea l i j ≤ LinearContainerArea l p q

end Algorithms.container_with_most_water_linear.lean
