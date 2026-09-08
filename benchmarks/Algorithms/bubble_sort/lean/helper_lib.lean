import AUXLib.Sorting
import SimpleC.SL.SeparationLogic

namespace Algorithms.bubble_sort.lean

open AUXLib.Sorting

def prefix_suffix_sorted (preList suffix : List Int) : Prop :=
  ∀ x, x ∈ preList → lowerbound x suffix

end Algorithms.bubble_sort.lean
