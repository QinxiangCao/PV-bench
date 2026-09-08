import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.house_robber.lean

open AUXLib MaxMinLib

def NonAdjacentIndexList (limit : Int) (picks : List Int) : Prop :=
  0 ≤ limit ∧ NoDup picks ∧ Forall (fun i => 0 ≤ i ∧ i < limit) picks ∧
  ∀ i j : Int, i ∈ picks → j ∈ picks → i ≠ j → 2 ≤ Z.abs (i - j)

def RobPlanValue (l picks : List Int) : Int := sum (picks.map (fun i => Znth i l 0))

def RobPrefixValue (l : List Int) (len value : Int) : Prop :=
  ∃ picks, (0 ≤ len ∧ len ≤ Zlength l) ∧ NonAdjacentIndexList len picks ∧
    value = RobPlanValue l picks

def HouseRobberAnswer (l : List Int) (answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun value => RobPrefixValue l (Zlength l) value)
    (fun value => value) answer

end Algorithms.house_robber.lean
