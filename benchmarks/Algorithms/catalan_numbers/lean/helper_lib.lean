import Algorithms.catalan_numbers.lean.spec_lib

namespace Algorithms.catalan_numbers.lean

open AUXLib

def StackRowProgress (n : Int) (table : List Int) (row col : Int) : Prop :=
  0 ≤ row ∧ (0 ≤ col ∧ col ≤ n + 1) ∧ StackTablePrefix n table (row * (n + 1) + col)

end Algorithms.catalan_numbers.lean
