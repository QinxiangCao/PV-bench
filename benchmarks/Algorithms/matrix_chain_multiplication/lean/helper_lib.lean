import Algorithms.matrix_chain_multiplication.lean.spec_lib

namespace Algorithms.matrix_chain_multiplication.lean

open AUXLib MaxMinLib

def MatrixChainZeroPrefix (table : List Int) (done : Int) : Prop :=
  Zlength table = done ∧ ∀ index : Int, (0 ≤ index ∧ index < done) → Znth index table 0 = 0

def MatrixChainTableValuesBounded (table : List Int) : Prop :=
  ∀ index : Int, (0 ≤ index ∧ index < Zlength table) →
    (0 ≤ Znth index table 0 ∧ Znth index table 0 ≤ 7000000)

def MatrixChainLengthsDone (dimensions table : List Int) (matrix_count next_length : Int) : Prop :=
  1 ≤ next_length ∧ ∀ length left right : Int,
    (1 ≤ length ∧ length < next_length) → right = left + length - 1 → 0 ≤ left →
    left + length ≤ matrix_count →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * matrix_count + right) table 0)

def MatrixChainLeftProgress (dimensions table : List Int) (matrix_count length next_left : Int) : Prop :=
  MatrixChainLengthsDone dimensions table matrix_count length ∧ ∀ left right : Int,
    (0 ≤ left ∧ left < next_left) → right = left + length - 1 → left + length ≤ matrix_count →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * matrix_count + right) table 0)

def MatrixChainSplitCandidate (dimensions table : List Int) (width left right split candidate : Int) : Prop :=
  candidate = Znth (left * width + split) table 0 + Znth ((split + 1) * width + right) table 0 +
    Znth left dimensions 0 * Znth (split + 1) dimensions 0 * Znth (right + 1) dimensions 0

def MatrixChainSplitProgress (dimensions table : List Int)
    (matrix_count width length left next_split best : Int) : Prop :=
  MatrixChainLeftProgress dimensions table matrix_count length left ∧
  let right := left + length - 1
  MaxMinLib.min_value_of_subset (· ≤ ·)
    (fun candidate => ∃ split : Int, (left ≤ split ∧ split < next_split) ∧
      MatrixChainSplitCandidate dimensions table width left right split candidate)
    (fun candidate => candidate) best

end Algorithms.matrix_chain_multiplication.lean
