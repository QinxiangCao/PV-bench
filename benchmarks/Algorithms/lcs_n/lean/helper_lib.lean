import Algorithms.lcs_n.lean.spec_lib

namespace Algorithms.lcs_n.lean

open AUXLib
abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none

def LCSNLogicalTableShape (mixed : List (Option Int)) (table : List Int) (n : Int) : Prop :=
  Zlength mixed = (n + 1) * (n + 1) ∧ Zlength table = (n + 1) * (n + 1)

def LCSNCellInitialized (mixed : List (Option Int)) (table : List Int) (n row col : Int) : Prop :=
  Znth (LCSNCellIndex n row col) mixed none = some (Znth (LCSNCellIndex n row col) table 0)

def LCSNBoundaryCell (mixed : List (Option Int)) (table : List Int) (n row col : Int) : Prop :=
  LCSNCellInitialized mixed table n row col ∧ Znth (LCSNCellIndex n row col) table 0 = 0

def LCSNInteriorCell (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row col : Int) : Prop :=
  LCSNCellInitialized mixed table n row col ∧ LCSNCellRecurrence xs ys table n row col ∧
    (0 ≤ Znth (LCSNCellIndex n row col) table 0 ∧
     Znth (LCSNCellIndex n row col) table 0 ≤ min row col)

def LCSNCellUndefined (mixed : List (Option Int)) (n row col : Int) : Prop :=
  Znth (LCSNCellIndex n row col) mixed none = none

def LCSNBoundariesReady (mixed : List (Option Int)) (table : List Int) (n : Int) : Prop :=
  (∀ row, (0 ≤ row ∧ row ≤ n) → LCSNBoundaryCell mixed table n row 0) ∧
  (∀ col, (0 ≤ col ∧ col ≤ n) → LCSNBoundaryCell mixed table n 0 col)

def LCSNCompletedInteriorRows (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n rows_done : Int) : Prop :=
  ∀ row col, (1 ≤ row ∧ row < rows_done) → (1 ≤ col ∧ col ≤ n) →
    LCSNInteriorCell xs ys mixed table n row col

def LCSNInteriorRowsUndefinedFrom (mixed : List (Option Int)) (n rows_from : Int) : Prop :=
  ∀ row col, (rows_from ≤ row ∧ row ≤ n) → (1 ≤ col ∧ col ≤ n) →
    LCSNCellUndefined mixed n row col

def LCSNColumnProgress (mixed : List (Option Int)) (table : List Int) (n rows_done : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧
  (∀ row, (0 ≤ row ∧ row < rows_done) → LCSNBoundaryCell mixed table n row 0) ∧
  (∀ row, (rows_done ≤ row ∧ row ≤ n) → LCSNCellUndefined mixed n row 0) ∧
  (∀ row col, (0 ≤ row ∧ row ≤ n) → (1 ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n row col)

def LCSNBoundaryProgress (mixed : List (Option Int)) (table : List Int) (n cols_done : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧
  (∀ row, (0 ≤ row ∧ row ≤ n) → LCSNBoundaryCell mixed table n row 0) ∧
  (∀ col, (1 ≤ col ∧ col < cols_done) → LCSNBoundaryCell mixed table n 0 col) ∧
  (∀ col, (cols_done ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n 0 col) ∧
  (∀ row col, (1 ≤ row ∧ row ≤ n) → (1 ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n row col)

def LCSNRowsProgress (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n rows_done : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧ LCSNBoundariesReady mixed table n ∧
  LCSNCompletedInteriorRows xs ys mixed table n rows_done ∧
  LCSNInteriorRowsUndefinedFrom mixed n rows_done

def LCSNRowProgress (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row next_col : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧ LCSNBoundariesReady mixed table n ∧
  LCSNCompletedInteriorRows xs ys mixed table n row ∧
  (∀ col, (1 ≤ col ∧ col < next_col) → LCSNInteriorCell xs ys mixed table n row col) ∧
  (∀ col, (next_col ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n row col) ∧
  LCSNInteriorRowsUndefinedFrom mixed n (row + 1)

end Algorithms.lcs_n.lean
