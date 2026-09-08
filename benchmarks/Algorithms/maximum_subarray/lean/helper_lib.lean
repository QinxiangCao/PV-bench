import Algorithms.maximum_subarray.lean.spec_lib

namespace Algorithms.maximum_subarray.lean

open AUXLib MaxMinLib

def max_Z (a b : Int) : Int := max a b

def MaxSuffixSumPrefix (l : List Int) (i ans : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun lo : Int => 0 ≤ lo ∧ lo < i)
    (fun lo => sum (sublist lo i l)) ans

end Algorithms.maximum_subarray.lean
