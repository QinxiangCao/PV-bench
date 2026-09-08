import Codeforces.examples_shard01.P030_1220C_substring_game_in_the_lesson.lean.spec_lib

namespace Codeforces.examples_shard01.P030_1220C_substring_game_in_the_lesson.lean

open AUXLib

def PrefixMinimum (s : List Int) (k mn : Int) : Prop :=
  (0 ≤ k ∧ k ≤ Zlength s) ∧ ((k = 0 ∧ mn = 123) ∨
    (0 < k ∧ (∃ j, (0 ≤ j ∧ j < k) ∧ mn = Znth j s 0) ∧ ∀ j, (0 ≤ j ∧ j < k) → mn ≤ Znth j s 0))

def SpecPrefix (s : List Int) (k : Int) (out : List Int) : Prop :=
  Zlength out = k ∧ ∀ i, (0 ≤ i ∧ i < k) →
    ((Znth i out 0 = 1 ∧ AnnWins s i) ∨ (Znth i out 0 = 0 ∧ ¬ AnnWins s i))

end Codeforces.examples_shard01.P030_1220C_substring_game_in_the_lesson.lean
