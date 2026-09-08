import Codeforces.examples_shard01.P039_435B_pasha_maximizes.lean.spec_lib

namespace Codeforces.examples_shard01.P039_435B_pasha_maximizes.lean

open AUXLib

def LexLe (a b : List Int) : Prop :=
  a = b ∨ (∃ i, (0 ≤ i ∧ i < min (Zlength a) (Zlength b)) ∧
    (∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = Znth j b 0) ∧ Znth i a 0 < Znth i b 0) ∨
    (Zlength a < Zlength b ∧ ListLib.is_prefix a b)

def PrefixEq (a b : List Int) (i : Int) : Prop :=
  Zlength a = Zlength b ∧ (0 ≤ i ∧ i ≤ Zlength a) ∧ ∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = Znth j b 0

def GreedyProgress (input : List Int) (budget : Int) (current : List Int) (pos remaining : Int) : Prop :=
  Zlength current = Zlength input ∧ (0 ≤ pos ∧ pos ≤ Zlength input) ∧ (0 ≤ remaining ∧ remaining ≤ budget) ∧
    SwapReach input current (budget - remaining) ∧
    ∀ q, SwapReach input q budget → LexLe q current ∨ (PrefixEq q current pos ∧ SwapReach current q remaining)

def FirstMaximumPrefix (l : List Int) (lo hi best : Int) : Prop :=
  (0 ≤ lo ∧ lo < hi) ∧ hi ≤ Zlength l ∧ (lo ≤ best ∧ best < hi) ∧
    (∀ p, (lo ≤ p ∧ p < hi) → Znth p l 0 ≤ Znth best l 0) ∧
    (∀ p, (lo ≤ p ∧ p < best) → Znth p l 0 < Znth best l 0)

def ReachableFirstMaximum (l : List Int) (pos remaining best : Int) : Prop :=
  FirstMaximumPrefix l pos (min (Zlength l) (pos + remaining + 1)) best

def move_left (l : List Int) («from» «to» : Int) : List Int :=
  sublist 0 «to» l ++ [Znth «from» l 0] ++ sublist «to» «from» l ++ sublist («from» + 1) (Zlength l) l

def GreedyExchangeClosure (current : List Int) (pos remaining best : Int) : Prop :=
  let moved := move_left current best pos
  let residual := remaining - (best - pos)
  (∀ q, LexLe q current → LexLe q moved) ∧
    (∀ q, PrefixEq q current pos → SwapReach current q remaining →
      LexLe q moved ∨ (PrefixEq q moved (pos + 1) ∧ SwapReach moved q residual))

def GreedySelectionReady (current : List Int) (pos remaining : Int) : Prop :=
  ∀ best, ReachableFirstMaximum current pos remaining best → GreedyExchangeClosure current pos remaining best

end Codeforces.examples_shard01.P039_435B_pasha_maximizes.lean
