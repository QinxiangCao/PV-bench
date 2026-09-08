import AUXLib.Sorting
import SimpleC.SL.SeparationLogic

namespace Algorithms.counting_sort.lean

open AUXLib
abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none
abbrev _App_option_Z := Option Int

def CountingZeroedPrefix (mixed_counts : List (Option Int)) (upto : Int) : Prop :=
  ∀ value, (0 ≤ value ∧ value < upto) → Znth value mixed_counts none = some 0

def CountingFrequency (values : List Int) (value : Int) : Int :=
  (values.count value : Int)

def CountingHistogramPrefix (input counts : List Int) (processed : Int) : Prop :=
  ∀ value, (0 ≤ value ∧ value < 100) →
    Znth value counts 0 = CountingFrequency (sublist 0 processed input) value

def CountingCumulativeEnd (input : List Int) (value : Int) : Int :=
  List.foldr (· + ·) 0 ((List.range (value + 1).toNat).map
    (fun index : Nat => CountingFrequency input ((index : Int))))

def CountingCumulativeState (input positions : List Int) (next_value : Int) : Prop :=
  ∀ value, (0 ≤ value ∧ value < 100) → Znth value positions 0 =
    if value < next_value then CountingCumulativeEnd input value else CountingFrequency input value

def CountingSorted (input sorted : List Int) : Prop :=
  Permutation input sorted ∧ AUXLib.Sorting.increasing sorted

def CountingBucketStart (input : List Int) (value : Int) : Int :=
  if value ≤ 0 then 0 else CountingCumulativeEnd input (value - 1)

def CountingPlacementProgress (input positions bucket_ends : List Int)
    (mixed_output : List (Option Int)) (sorted : List Int) (next_index : Int) : Prop :=
  CountingSorted input sorted ∧
  (∀ value, (0 ≤ value ∧ value < 100) →
    Znth value bucket_ends 0 = CountingCumulativeEnd input value) ∧
  (∀ value, (0 ≤ value ∧ value < 100) →
    Znth value positions 0 = CountingBucketStart input value +
      CountingFrequency (sublist 0 (next_index + 1) input) value) ∧
  (∀ value index, (0 ≤ value ∧ value < 100) →
    (Znth value positions 0 ≤ index ∧ index < Znth value bucket_ends 0) →
    Znth index mixed_output none = some (Znth index sorted 0))

def CountingCopyProgress (before target live : List Int) (copied : Int) : Prop :=
  live = sublist 0 copied target ++ sublist copied (Zlength before) before

end Algorithms.counting_sort.lean
