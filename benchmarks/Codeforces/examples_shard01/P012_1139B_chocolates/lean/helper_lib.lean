import Codeforces.examples_shard01.P012_1139B_chocolates.lean.spec_lib

namespace Codeforces.examples_shard01.P012_1139B_chocolates.lean

open AUXLib

open MaxMinLib

def DominantPurchase (a x : List Int) : Prop :=
  FeasiblePurchase a x ∧ ∀ y, FeasiblePurchase a y → ∀ k, (0 ≤ k ∧ k < Zlength a) → Znth k y 0 ≤ Znth k x 0

def SuffixDominantState (a : List Int) (lo total prev : Int) : Prop :=
  ∃ x, DominantPurchase (sublist lo (Zlength a) a) x ∧
    total = x.foldr (· + ·) 0 ∧ (lo = Zlength a → prev = 0) ∧ (lo < Zlength a → prev = Znth 0 x 0)

end Codeforces.examples_shard01.P012_1139B_chocolates.lean
