import Algorithms.choosing_inns.lean.spec_lib

namespace Algorithms.choosing_inns.lean

open AUXLib

def color_count (colors : List Int) (limit color : Int) : Int :=
  Int.ofNat ((zrange limit).filter (fun idx => decide (Znth idx colors 0 = color))).length

def good_color_count (colors costs : List Int) (limit p color : Int) : Int :=
  Int.ofNat ((zrange limit).filter (fun idx => decide (Znth idx colors 0 = color) &&
    affordable_betweenb costs p idx (limit - 1))).length

def CountArraySafe (xs : List Int) (k limit : Int) : Prop :=
  Zlength xs = k ∧ ∀ idx, (0 ≤ idx ∧ idx < k) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ limit

def CountsZeroPrefix (xs : List Int) (written : Int) : Prop :=
  Zlength xs = written ∧ ∀ idx, (0 ≤ idx ∧ idx < written) → Znth idx xs 0 = 0

def CountsZeroFull (k : Int) (xs : List Int) : Prop :=
  Zlength xs = k ∧ ∀ idx, (0 ≤ idx ∧ idx < k) → Znth idx xs 0 = 0

def CopyCountsPrefix (src old dst : List Int) (written k : Int) : Prop :=
  (∀ idx, (0 ≤ idx ∧ idx < written) → Znth idx dst 0 = Znth idx src 0) ∧
  (∀ idx, (written ≤ idx ∧ idx < k) → Znth idx dst 0 = Znth idx old 0)

def ChoosingPrefixDataSafe (colors costs : List Int) (limit k : Int) (seen good : List Int) : Prop :=
  (0 ≤ limit ∧ limit ≤ Zlength colors) ∧ Zlength costs = Zlength colors ∧
  CountArraySafe seen k limit ∧ CountArraySafe good k limit

def ChoosingPrefixState (colors costs : List Int) (limit k p answer : Int) (seen good : List Int) : Prop :=
  answer = choosing_pair_count colors costs p limit ∧
  (∀ color, (0 ≤ color ∧ color < k) → Znth color seen 0 = color_count colors limit color) ∧
  (∀ color, (0 ≤ color ∧ color < k) → Znth color good 0 = good_color_count colors costs limit p color)

end Algorithms.choosing_inns.lean
