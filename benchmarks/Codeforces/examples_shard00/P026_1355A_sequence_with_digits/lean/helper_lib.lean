import Codeforces.examples_shard00.P026_1355A_sequence_with_digits.lean.spec_lib

namespace Codeforces.examples_shard00.P026_1355A_sequence_with_digits.lean

open AUXLib
open MaxMinLib

def DigitExtrema (digits : List Int) (lo hi : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) lo ∧
    max_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) hi

def DigitScanState (original remaining mn mx : Int) : Prop :=
  ∃ pending processed, DecimalDigitsOf original (pending ++ processed) ∧
    remaining = pending.foldl (fun value digit => 10 * value + digit) 0 ∧
    ((processed = [] ∧ mn = 9 ∧ mx = 0) ∨ (processed ≠ [] ∧ DigitExtrema processed mn mx))

def SequencePrefix (a1 count current : Int) : Prop :=
  ∃ values, Zlength values = count ∧ Znth 0 values 0 = a1 ∧ Znth (count - 1) values 0 = current ∧
    ∀ i, (0 ≤ i ∧ i < count - 1) → DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0)

end Codeforces.examples_shard00.P026_1355A_sequence_with_digits.lean
