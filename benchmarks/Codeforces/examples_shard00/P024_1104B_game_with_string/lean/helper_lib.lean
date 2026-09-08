import Codeforces.examples_shard00.P024_1104B_game_with_string.lean.spec_lib

namespace Codeforces.examples_shard00.P024_1104B_game_with_string.lean

open AUXLib

def PairDeletionTraceTo (initial final : List Int) (moves : Int) : Prop :=
  0 ≤ moves ∧ ∃ states, Zlength states = moves + 1 ∧ Znth 0 states [] = initial ∧ Znth moves states [] = final ∧
    (∀ k, (0 ≤ k ∧ k < moves) → OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states []))

def PairDeletionIrreducible (s : List Int) : Prop := ∀ next, ¬ OneEqualPairDeletion s next

def PrefixGameState («prefix» reduced : List Int) (moves : Int) : Prop :=
  PairDeletionTraceTo «prefix» reduced moves ∧ PairDeletionIrreducible reduced ∧
    (∀ states, DeletionGameTrace «prefix» states → Zlength states = moves + 1)

end Codeforces.examples_shard00.P024_1104B_game_with_string.lean
