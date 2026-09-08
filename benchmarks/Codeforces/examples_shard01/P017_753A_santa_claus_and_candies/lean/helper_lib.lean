import Codeforces.examples_shard01.P017_753A_santa_claus_and_candies.lean.spec_lib

namespace Codeforces.examples_shard01.P017_753A_santa_claus_and_candies.lean

open AUXLib

open MaxMinLib

def triangular (k : Int) : Int := Z.div (k * (k + 1)) 2

def CandyPrefix (i : Int) (xs : List Int) : Prop :=
  Zlength xs = i ∧ ∀ j, (0 ≤ j ∧ j < i) → Znth j xs 0 = j + 1

def GreedyCandyPlan (n k : Int) (xs : List Int) : Prop :=
  Zlength xs = k ∧ (∀ j, (0 ≤ j ∧ j < k - 1) → Znth j xs 0 = j + 1) ∧
  Znth (k - 1) xs 0 = k + (n - triangular k)

end Codeforces.examples_shard01.P017_753A_santa_claus_and_candies.lean
