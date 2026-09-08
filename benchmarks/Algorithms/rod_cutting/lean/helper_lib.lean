import Algorithms.rod_cutting.lean.spec_lib

namespace Algorithms.rod_cutting.lean

open AUXLib MaxMinLib

def RodCutScanBest (price revenue : List Int) (rod_len next_piece best : Int) : Prop :=
  MaxMinLib.max_value_of_subset_with_default (· ≤ ·)
    (fun piece : Int => 1 ≤ piece ∧ piece < next_piece)
    (fun piece => Znth piece price 0 + Znth (rod_len - piece) revenue 0) 0 best

end Algorithms.rod_cutting.lean
