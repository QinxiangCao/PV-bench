import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.container_with_most_water_linear.lean

open AUXLib

def LinearContainerHeight (l : List Int) (i j : Int) : Int := min (Znth i l 0) (Znth j l 0)

def LinearContainerArea (l : List Int) (i j : Int) : Int := (j-i) * LinearContainerHeight l i j

def LinearContainerPair (l : List Int) (i j : Int) : Prop := 0 ≤ i ∧ i < j ∧ j < Zlength l

def MaximumContainerArea (l : List Int) (ans : Int) : Prop :=
  (∃ i j, LinearContainerPair l i j ∧ ans = LinearContainerArea l i j) ∧
  ∀ i j, LinearContainerPair l i j → LinearContainerArea l i j ≤ ans

end Algorithms.container_with_most_water_linear.lean
