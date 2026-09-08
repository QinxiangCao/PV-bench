import Algorithms.concatenating_numbers.lean.spec_lib

namespace Algorithms.concatenating_numbers.lean

open AUXLib

def digit_lex_gt (xs ys : List Int) : Prop :=
  Zlength xs = Zlength ys ∧
  ∃ k, (0 ≤ k ∧ k < Zlength xs) ∧
    (∀ j, (0 ≤ j ∧ j < k) → Znth j xs 0 = Znth j ys 0) ∧
    Znth k ys 0 < Znth k xs 0

def item_at (rows : List (List Int)) (lengths : List Int) (i : Int) :
  number_item :=
  (Znth i rows [], Znth i lengths 0)

def item_before
    (rows : List (List Int)) (lengths : List Int) (i j : Int) : Prop :=
  digit_lex_gt
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i))

def item_before_or_equal
    (rows : List (List Int)) (lengths : List Int) (i j : Int) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i))

def ConcatLeftDigit
    (rows : List (List Int)) (lens : List Int) (i j position : Int) : Int :=
  Znth position
    (item_digits (item_at rows lens i) ++
     item_digits (item_at rows lens j)) 0

def ConcatRightDigit
    (rows : List (List Int)) (lens : List Int) (i j position : Int) : Int :=
  Znth position
    (item_digits (item_at rows lens j) ++
     item_digits (item_at rows lens i)) 0

def SameOutsidePairedRange
    (rows0 rows1 : List (List Int)) (lens0 lens1 : List Int)
    (left right : Int) : Prop :=
  Zlength rows0 = Zlength rows1 ∧
  Zlength lens0 = Zlength lens1 ∧
  ∀ k, (0 ≤ k ∧ k < Zlength rows0) →
    (k < left ∨ right < k) →
    item_at rows1 lens1 k = item_at rows0 lens0 k

def ConcatComparePrefix
    (rows : List (List Int)) (lens : List Int)
    (i j position : Int) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j);
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i);
  (0 ≤ position ∧ position ≤ Zlength lhs) ∧
  Zlength lhs = Zlength rhs ∧
  ∀ k, (0 ≤ k ∧ k < position) → Znth k lhs 0 = Znth k rhs 0

def ConcatCompareOutcome
    (rows : List (List Int)) (lens : List Int)
    (i j comparison : Int) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j);
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i);
  (comparison = 0 ∧ lhs = rhs) ∨
  (∃ k, (0 ≤ k ∧ k < Zlength lhs) ∧
     Zlength lhs = Zlength rhs ∧
     (∀ p, (0 ≤ p ∧ p < k) → Znth p lhs 0 = Znth p rhs 0) ∧
     Znth k lhs 0 ≠ Znth k rhs 0 ∧
     comparison = Znth k lhs 0 - Znth k rhs 0)

def SwapRowsPrefix
    (before after : List (List Int)) (first second progress width : Int) : Prop :=
  let first_row := Znth first before [];
  let second_row := Znth second before [];
  let first_now := sublist 0 progress second_row ++
                   sublist progress width first_row;
  let second_now := sublist 0 progress first_row ++
                    sublist progress width second_row;
  after = replace_Znth second second_now
            (replace_Znth first first_now before)

def PartitionScanState
    (rows0 rows1 : List (List Int)) (lens0 lens1 : List Int)
    (low high boundary scan : Int) : Prop :=
  PairedPermutation rows0 rows1 lens0 lens1 ∧
  SameOutsidePairedRange rows0 rows1 lens0 lens1 low high ∧
  item_at rows1 lens1 high = item_at rows0 lens0 high ∧
  (∀ k, (low ≤ k ∧ k ≤ boundary) → item_before rows1 lens1 k high) ∧
  (∀ k, (boundary < k ∧ k < scan) → ¬ item_before rows1 lens1 k high)

def GreedyPartitionedAt
    (rows : List (List Int)) (lens : List Int)
    (low high pivot : Int) : Prop := (low ≤ pivot ∧ pivot ≤ high) ∧
  (∀ k, (low ≤ k ∧ k < pivot) → item_before rows lens k pivot) ∧
  (∀ k, (pivot < k ∧ k ≤ high) → ¬ item_before rows lens k pivot)

def GreedySortedRange
    (rows : List (List Int)) (lens : List Int) (left right : Int) : Prop :=
  ∀ i j,
    left ≤ i ∧ i ≤ j ∧ j ≤ right →
    item_before_or_equal rows lens i j

def GreedySorted
    (rows : List (List Int)) (lens : List Int) : Prop :=
  ∀ i j,
    0 ≤ i ∧ i ≤ j ∧ j < Zlength rows →
    item_before_or_equal rows lens i j

def ConcatenatedPrefix
    (rows : List (List Int)) (lens : List Int) (row_count : Int) : List Int :=
  concatenate_rows (sublist 0 row_count rows) (sublist 0 row_count lens)

def ConcatenatedOutputPrefix
    (rows : List (List Int)) (lens : List Int)
    (row_count digit_count : Int) : List Int :=
  ConcatenatedPrefix rows lens row_count ++
  sublist 0 digit_count (Znth row_count rows [])

end Algorithms.concatenating_numbers.lean
