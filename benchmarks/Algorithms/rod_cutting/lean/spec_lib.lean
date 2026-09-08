import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.rod_cutting.lean

open AUXLib MaxMinLib

def RodCutPlan (rod_len : Int) (pieces : List Int) : Prop :=
  0 ≤ rod_len ∧ Forall (fun piece => 1 ≤ piece ∧ piece ≤ rod_len) pieces ∧ sum pieces = rod_len

def RodCutPlanRevenue (price pieces : List Int) : Int :=
  sum (pieces.map (fun piece => Znth piece price 0))

def RodCutOptimalRevenue (price : List Int) (rod_len answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun pieces : List Int => RodCutPlan rod_len pieces)
    (fun pieces => RodCutPlanRevenue price pieces) answer

def RodCutRevenueTable (price revenue : List Int) (upto : Int) : Prop :=
  ∀ rod_len : Int, (0 ≤ rod_len ∧ rod_len < upto) →
    RodCutOptimalRevenue price rod_len (Znth rod_len revenue 0)

end Algorithms.rod_cutting.lean
