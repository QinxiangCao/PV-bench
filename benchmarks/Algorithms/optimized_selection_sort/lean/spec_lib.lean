import AUXLib.Sorting
import SimpleC.SL.SeparationLogic

namespace Algorithms.optimized_selection_sort.lean

export AUXLib.Sorting (increasing_aux increasing lowerbound strict_lowerbound)
open AUXLib

def optimized_selection_sort_result (input output : List Int) : Prop :=
  Permutation input output ∧ increasing output

end Algorithms.optimized_selection_sort.lean
