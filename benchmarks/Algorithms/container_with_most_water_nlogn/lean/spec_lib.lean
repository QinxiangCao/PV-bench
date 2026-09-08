import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.container_with_most_water_nlogn.lean

open AUXLib MaxMinLib

def MaximumContainerArea (l : List Int) (ans : Int) : Prop :=
  ∃ i j, 0 ≤ i ∧ i < j ∧ j < Zlength l ∧ ans = (j-i) * min (Znth i l 0) (Znth j l 0) ∧
    ∀ p q, 0 ≤ p → p < q → q < Zlength l → (q-p) * min (Znth p l 0) (Znth q l 0) ≤ ans

def IndexedHeightsNLogN (l : List Int) : List (Int × Int) :=
  (List.range l.length).map (fun k : Nat => (l.getD k 0, (k : Int)))

def HeightIndexPermutationNLogN (l heights indices : List Int) : Prop :=
  Zlength heights = Zlength l ∧ Zlength indices = Zlength l ∧ List.Perm (heights.zip indices) (IndexedHeightsNLogN l)

def HeightIndexRangeDescendingNLogN (heights : List Int) (lo hi : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ Zlength heights ∧ ∀ p q, lo ≤ p → p ≤ q → q < hi → Znth q heights 0 ≤ Znth p heights 0

def SortedHeightIndexWorkspaceNLogN (l heights indices : List Int) : Prop :=
  HeightIndexPermutationNLogN l heights indices ∧ HeightIndexRangeDescendingNLogN heights 0 (Zlength heights)

end Algorithms.container_with_most_water_nlogn.lean
