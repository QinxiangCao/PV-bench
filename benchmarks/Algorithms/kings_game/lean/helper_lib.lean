import Algorithms.kings_game.lean.spec_lib

namespace Algorithms.kings_game.lean

open AUXLib MaxMinLib

def minister_swap (ps : List minister) (i j : Int) : List minister :=
  replace_Znth j (Znth i ps default_minister) (replace_Znth i (Znth j ps default_minister) ps)

def minister_swap_flat (flat : List Int) (i j : Int) : List Int :=
  let il := Znth (2 * i) flat 0
  let ir := Znth (2 * i + 1) flat 0
  let jl := Znth (2 * j) flat 0
  let jr := Znth (2 * j + 1) flat 0
  replace_Znth (2 * j + 1) ir (replace_Znth (2 * j) il (replace_Znth (2 * i + 1) jr (replace_Znth (2 * i) jl flat)))

def BubbleOuterProperty (ps : List minister) (n pass : Int) : Prop :=
  Zlength ps = n ∧
  (∀ i j, n - pass ≤ i → i ≤ j → j < n → MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister)) ∧
  (∀ i j, 0 ≤ i → i < n - pass → n - pass ≤ j → j < n → MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister))

def BubbleScanProperty (ps : List minister) (n pass j : Int) : Prop :=
  (0 ≤ j ∧ j < n - pass) ∧ ∀ k, 0 ≤ k → k ≤ j → MinisterProductLe (Znth k ps default_minister) (Znth j ps default_minister)

end Algorithms.kings_game.lean
