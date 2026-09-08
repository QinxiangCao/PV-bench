import Algorithms.house_robber.lean.spec_lib

namespace Algorithms.house_robber.lean

open AUXLib MaxMinLib

def RobPrefixOpt (l : List Int) (len answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun value => RobPrefixValue l len value)
    (fun value => value) answer

def HouseRobberDPState (l : List Int) (i prev2 prev1 : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength l) ∧ RobPrefixOpt l i prev1 ∧
    ((i = 0 ∧ prev2 = 0) ∨ (0 < i ∧ RobPrefixOpt l (i - 1) prev2))

end Algorithms.house_robber.lean
