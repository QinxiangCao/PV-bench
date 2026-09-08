import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ZParity

namespace Codeforces.examples_shard00.P024_1104B_game_with_string.lean

open AUXLib

def OneEqualPairDeletion (before after : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength before - 1) ∧ Znth i before 0 = Znth (i + 1) before 0 ∧
    after = sublist 0 i before ++ sublist (i + 2) (Zlength before) before

def DeletionGameTrace (initial : List Int) (states : List (List Int)) : Prop :=
  0 < Zlength states ∧ Znth 0 states [] = initial ∧
  (∀ k, (0 ≤ k ∧ k < Zlength states - 1) → OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states [])) ∧
  (∀ next, ¬ OneEqualPairDeletion (Znth (Zlength states - 1) states []) next)

def FirstPlayerWinsDeletionGame (s : List Int) : Prop :=
  ∀ states, DeletionGameTrace s states → Z.even (Zlength states - 1) = false

def Pre (s : List Int) : Prop :=
  (1 ≤ Zlength s ∧ Zlength s ≤ 100000) ∧ Forall (fun c => 97 ≤ c ∧ c ≤ 122) s

def Spec (s : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ FirstPlayerWinsDeletionGame s)

end Codeforces.examples_shard00.P024_1104B_game_with_string.lean
