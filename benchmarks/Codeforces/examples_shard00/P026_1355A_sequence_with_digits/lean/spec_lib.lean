import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface

namespace Codeforces.examples_shard00.P026_1355A_sequence_with_digits.lean

open AUXLib
open MaxMinLib

def DecimalDigitsOf (x : Int) (digits : List Int) : Prop :=
  0 < Zlength digits ∧ Forall (fun d => 0 ≤ d ∧ d ≤ 9) digits ∧ Znth 0 digits 0 ≠ 0 ∧
    x = digits.foldl (fun value digit => 10 * value + digit) 0

def DigitRecurrenceStep (x y : Int) : Prop :=
  ∃ digits lo hi, DecimalDigitsOf x digits ∧
    min_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) lo ∧
    max_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) hi ∧ y = x + lo * hi

def Pre (a1 k : Int) : Prop :=
  (1 ≤ a1 ∧ a1 ≤ 1000000000000000000) ∧ (1 ≤ k ∧ k ≤ 10000000000000000)

def Spec (a1 k out : Int) : Prop :=
  ∃ values, Zlength values = k ∧ Znth 0 values 0 = a1 ∧ Znth (k - 1) values 0 = out ∧
    ∀ i, (0 ≤ i ∧ i < k - 1) → DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0)

end Codeforces.examples_shard00.P026_1355A_sequence_with_digits.lean
