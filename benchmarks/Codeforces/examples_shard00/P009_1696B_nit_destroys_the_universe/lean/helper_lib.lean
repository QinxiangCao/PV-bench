import Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe.lean.spec_lib

namespace Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe.lean

open AUXLib

def NonzeroStartAt (a : List Int) (i : Int) : Prop :=
  (0 ≤ i ∧ i < Zlength a) ∧ Znth i a 0 ≠ 0 ∧ (i = 0 ∨ Znth (i - 1) a 0 = 0)

def PrefixRunCount (a : List Int) (upto runs : Int) : Prop :=
  ∃ starts : List Int, Zlength starts = runs ∧ starts.Nodup ∧
    ∀ i, i ∈ starts ↔ (0 ≤ i ∧ i < upto) ∧ NonzeroStartAt a i

def PrefixTailState (a : List Int) (upto inside : Int) : Prop :=
  (upto = 0 ∧ inside = 0) ∨ ((0 < upto ∧ upto ≤ Zlength a) ∧
    ((inside = 0 ∧ Znth (upto - 1) a 0 = 0) ∨ (inside = 1 ∧ Znth (upto - 1) a 0 ≠ 0)))

def ScanState (a : List Int) (upto runs inside : Int) : Prop :=
  PrefixRunCount a upto runs ∧ PrefixTailState a upto inside

end Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe.lean
