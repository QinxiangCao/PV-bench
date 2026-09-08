import Algorithms.split_array_largest_sum.lean.spec_lib

namespace Algorithms.split_array_largest_sum.lean

open AUXLib MaxMinLib

inductive PrefixSplitState (l : List Int) (cap : Int) : Int → Int → Int → Prop
  | PrefixSplitState_zero : 0 ≤ cap → PrefixSplitState l cap 0 1 0
  | PrefixSplitState_new_segment : ∀ i cnt cur,
      (0 ≤ i ∧ i < Zlength l) → (0 ≤ Znth i l 0 ∧ Znth i l 0 ≤ cap) →
      cur + Znth i l 0 > cap → PrefixSplitState l cap i cnt cur →
      PrefixSplitState l cap (i + 1) (cnt + 1) (Znth i l 0)
  | PrefixSplitState_extend : ∀ i cnt cur,
      (0 ≤ i ∧ i < Zlength l) → (0 ≤ Znth i l 0 ∧ Znth i l 0 ≤ cap) →
      cur + Znth i l 0 ≤ cap → PrefixSplitState l cap i cnt cur →
      PrefixSplitState l cap (i + 1) cnt (cur + Znth i l 0)

export PrefixSplitState (PrefixSplitState_zero PrefixSplitState_new_segment PrefixSplitState_extend)

def CanSplit (l : List Int) (m cap : Int) : Prop :=
  ∃ cnt cur, PrefixSplitState l cap (Zlength l) cnt cur ∧ cnt ≤ m

def CannotSplit (l : List Int) (m cap : Int) : Prop :=
  ∀ cnt cur, PrefixSplitState l cap (Zlength l) cnt cur → m < cnt

end Algorithms.split_array_largest_sum.lean
