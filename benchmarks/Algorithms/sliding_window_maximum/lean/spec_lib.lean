import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.sliding_window_maximum.lean

open AUXLib

def SWMInputSafe (l : List Int) (n k : Int) : Prop :=
  1 ≤ k ∧ k ≤ n ∧ n ≤ 100000 ∧ Zlength l = n ∧
  ∀ idx, (0 ≤ idx ∧ idx < n) → -10000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 10000

def WindowMaxValue (l : List Int) (lo hi ans : Int) : Prop :=
  ∃ pos, (lo ≤ pos ∧ pos < hi) ∧ ans = Znth pos l 0 ∧
    ∀ idx, (lo ≤ idx ∧ idx < hi) → Znth idx l 0 ≤ ans

def SlidingWindowMaximum (l : List Int) (k : Int) (out : List Int) : Prop :=
  Zlength out = Zlength l-k+1 ∧
    ∀ idx, (0 ≤ idx ∧ idx < Zlength out) → WindowMaxValue l idx (idx+k) (Znth idx out 0)

end Algorithms.sliding_window_maximum.lean
