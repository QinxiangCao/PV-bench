import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.maximum_subarray.lean

open AUXLib MaxMinLib

def MaxSubarraySumPrefix (l : List Int) (i ans : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·)
    (fun p : Int × Int => let (lo, hi) := p; 0 ≤ lo ∧ lo < hi ∧ hi ≤ i)
    (fun p : Int × Int => let (lo, hi) := p; sum (sublist lo hi l)) ans

end Algorithms.maximum_subarray.lean
