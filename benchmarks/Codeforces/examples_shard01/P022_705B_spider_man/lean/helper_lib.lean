import Codeforces.examples_shard01.P022_705B_spider_man.lean.spec_lib

namespace Codeforces.examples_shard01.P022_705B_spider_man.lean

open AUXLib

def CycleMoveCount (added : List Int) : Int := added.foldr (· + ·) 0 - Zlength added

def SpiderWinnerCode (moves code : Int) : Prop :=
  (code = 1 ∧ Z.odd moves = true) ∨ (code = 2 ∧ Z.even moves = true)

def NextParity (par a next : Int) : Prop :=
  (0 ≤ par ∧ par ≤ 1) ∧ 1 ≤ a ∧ next = Z.rem (par + (a - 1)) 2

def SpiderPrefixState (added out : List Int) (par : Int) : Prop :=
  Zlength out = Zlength added ∧ (0 ≤ par ∧ par ≤ 1) ∧ par = Z.rem (CycleMoveCount added) 2 ∧
    ∀ i, (0 ≤ i ∧ i < Zlength added) → SpiderWinnerCode (CycleMoveCount (sublist 0 (i + 1) added)) (Znth i out 0)

end Codeforces.examples_shard01.P022_705B_spider_man.lean
