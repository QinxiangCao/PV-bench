import Algorithms.container_with_most_water_nlogn.lean.spec_lib

namespace Algorithms.container_with_most_water_nlogn.lean

open AUXLib MaxMinLib

def ContainerHeightNLogN (l : List Int) (i j : Int) : Int := min (Znth i l 0) (Znth j l 0)

def ContainerAreaNLogN (l : List Int) (i j : Int) : Int := (j-i) * ContainerHeightNLogN l i j

def ContainerPairNLogN (l : List Int) (i j : Int) : Prop := 0 ≤ i ∧ i < j ∧ j < Zlength l

def WorkspacePrefixNLogN (l heights indices : List Int) (k : Int) : Prop :=
  (∀ p, (0 ≤ p ∧ p < k) → Znth p heights 0 = Znth p l 0) ∧ (∀ p, (0 ≤ p ∧ p < k) → Znth p indices 0 = p)

def SameHeightIndexOutsideNLogN (before_h before_i after_h after_i : List Int) (lo hi : Int) : Prop :=
  Zlength after_h = Zlength before_h ∧ Zlength after_i = Zlength before_i ∧
    ∀ k, (0 ≤ k ∧ k < Zlength before_h) → (k < lo ∨ hi ≤ k) →
      Znth k after_h 0 = Znth k before_h 0 ∧ Znth k after_i 0 = Znth k before_i 0

def HeightIndexRangePermutationNLogN (before_h before_i after_h after_i : List Int) (lo hi : Int) : Prop :=
  List.Perm ((sublist lo hi after_h).zip (sublist lo hi after_i)) ((sublist lo hi before_h).zip (sublist lo hi before_i))

def HeightIndexRangeSortResultNLogN (before_h before_i after_h after_i : List Int) (lo hi : Int) : Prop :=
  Zlength before_h = Zlength before_i ∧ Zlength after_h = Zlength after_i ∧ 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ Zlength before_h ∧
    SameHeightIndexOutsideNLogN before_h before_i after_h after_i lo hi ∧
    HeightIndexRangePermutationNLogN before_h before_i after_h after_i lo hi ∧ HeightIndexRangeDescendingNLogN after_h lo hi

def MergePrefixStateNLogN (source_h source_i dest0_h dest0_i dest_h dest_i : List Int) (left middle right p q output : Int) : Prop :=
  HeightIndexRangeDescendingNLogN source_h left middle ∧ HeightIndexRangeDescendingNLogN source_h middle right ∧
    (∀ t, (0 ≤ t ∧ t < Zlength dest0_h) → (t < left ∨ output ≤ t) → Znth t dest_h 0 = Znth t dest0_h 0 ∧ Znth t dest_i 0 = Znth t dest0_i 0) ∧
    List.Perm ((sublist left output dest_h).zip (sublist left output dest_i))
      (((sublist left p source_h).zip (sublist left p source_i)) ++ ((sublist middle q source_h).zip (sublist middle q source_i))) ∧
    (∀ u v, left ≤ u → u ≤ v → v < output → Znth v dest_h 0 ≤ Znth u dest_h 0) ∧
    (∀ u v, (left ≤ u ∧ u < output) → ((p ≤ v ∧ v < middle) ∨ (q ≤ v ∧ v < right)) → Znth v source_h 0 ≤ Znth u dest_h 0)

def HeightIndexRangeMergeResultNLogN (source_h source_i dest0_h dest0_i dest_h dest_i : List Int) (left middle right : Int) : Prop :=
  0 ≤ left ∧ left ≤ middle ∧ middle ≤ right ∧ right ≤ Zlength source_h ∧
    SameHeightIndexOutsideNLogN dest0_h dest0_i dest_h dest_i left right ∧
    List.Perm ((sublist left right dest_h).zip (sublist left right dest_i)) ((sublist left right source_h).zip (sublist left right source_i)) ∧
    HeightIndexRangeDescendingNLogN dest_h left right

def CopyHeightIndexPrefixNLogN (source_h source_i dest0_h dest0_i dest_h dest_i : List Int) (left right k : Int) : Prop :=
  (∀ p, (left ≤ p ∧ p < k) → Znth p dest_h 0 = Znth p source_h 0 ∧ Znth p dest_i 0 = Znth p source_i 0) ∧
    (∀ p, (0 ≤ p ∧ p < Zlength dest0_h) → (p < left ∨ k ≤ p) → Znth p dest_h 0 = Znth p dest0_h 0 ∧ Znth p dest_i 0 = Znth p dest0_i 0)

def ProcessedIndexEndpointsNLogN (indices : List Int) (k minimum maximum : Int) : Prop :=
  (∃ p, (0 ≤ p ∧ p < k) ∧ Znth p indices 0 = minimum) ∧
  (∃ p, (0 ≤ p ∧ p < k) ∧ Znth p indices 0 = maximum) ∧
  (∀ p, (0 ≤ p ∧ p < k) → (minimum ≤ Znth p indices 0 ∧ Znth p indices 0 ≤ maximum))

def ProcessedContainerPairNLogN (l indices : List Int) (k : Int) (ij : Int × Int) : Prop :=
  ContainerPairNLogN l ij.1 ij.2 ∧ ij.1 ∈ sublist 0 k indices ∧ ij.2 ∈ sublist 0 k indices

def ProcessedContainerMaximumNLogN (l indices : List Int) (k ans : Int) : Prop :=
  max_value_of_subset_with_default (· ≤ ·) (ProcessedContainerPairNLogN l indices k)
    (fun ij : Int × Int => ContainerAreaNLogN l ij.1 ij.2) 0 ans

end Algorithms.container_with_most_water_nlogn.lean
