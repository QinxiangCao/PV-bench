import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.lcs_n.lean

open AUXLib

def LCSNCellIndex (n row col : Int) : Int := row * (n + 1) + col

def LCSNCellRecurrence (xs ys table : List Int) (n row col : Int) : Prop :=
  ((row = 0 ∨ col = 0) ∧ Znth (LCSNCellIndex n row col) table 0 = 0) ∨
  (0 < row ∧ 0 < col ∧
    ((Znth (row - 1) xs 0 = Znth (col - 1) ys 0 ∧
       Znth (LCSNCellIndex n row col) table 0 =
         Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1) ∨
     (Znth (row - 1) xs 0 ≠ Znth (col - 1) ys 0 ∧
       Znth (LCSNCellIndex n row col) table 0 =
         max (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0))))

def LCSNTableResult (xs ys : List Int) (n : Int) (table : List Int) : Prop :=
  Zlength table = (n + 1) * (n + 1) ∧ ∀ row col,
    (0 ≤ row ∧ row ≤ n) → (0 ≤ col ∧ col ≤ n) →
    LCSNCellRecurrence xs ys table n row col

end Algorithms.lcs_n.lean
