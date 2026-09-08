import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.matrix_chain_multiplication.lean

open AUXLib MaxMinLib

def MatrixChainDimensionsBounded (dimensions : List Int) (matrix_count : Int) : Prop :=
  Zlength dimensions = matrix_count + 1 ∧
    ∀ i : Int, (0 ≤ i ∧ i ≤ matrix_count) → (1 ≤ Znth i dimensions 0 ∧ Znth i dimensions 0 ≤ 100)

inductive MatrixChainPlan (dimensions : List Int) : Int → Int → Int → Prop where
  | MatrixChainPlan_single (left : Int) : 0 ≤ left → left + 1 < Zlength dimensions →
      MatrixChainPlan dimensions left left 0
  | MatrixChainPlan_join (left split right left_cost right_cost : Int) :
      0 ≤ left → (left ≤ split ∧ split < right) → right + 1 < Zlength dimensions →
      MatrixChainPlan dimensions left split left_cost →
      MatrixChainPlan dimensions (split + 1) right right_cost →
      MatrixChainPlan dimensions left right (left_cost + right_cost +
        Znth left dimensions 0 * Znth (split + 1) dimensions 0 * Znth (right + 1) dimensions 0)

export MatrixChainPlan (MatrixChainPlan_single MatrixChainPlan_join)

def MatrixChainIntervalMinimum (dimensions : List Int) (left right answer : Int) : Prop :=
  MaxMinLib.min_value_of_subset (· ≤ ·)
    (fun scalar_cost => MatrixChainPlan dimensions left right scalar_cost)
    (fun scalar_cost => scalar_cost) answer

def MatrixChainMinimumCost (dimensions : List Int) (matrix_count answer : Int) : Prop :=
  Zlength dimensions = matrix_count + 1 ∧ MatrixChainIntervalMinimum dimensions 0 (matrix_count - 1) answer

def MatrixChainTableResult (dimensions table : List Int) (matrix_count : Int) : Prop :=
  Zlength table = matrix_count * matrix_count ∧
  ∀ left right : Int, (0 ≤ left ∧ left ≤ right ∧ right < matrix_count) →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * matrix_count + right) table 0)

end Algorithms.matrix_chain_multiplication.lean
