import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean

open AUXLib

abbrev Some {A : Type u} (a : A) : Option A := some a

abbrev None {A : Type u} : Option A := none

def DecimalValue (digits : List Int) : Int := digits.foldl (fun value digit => 10 * value + digit) 0

def BadUglyDigits (n : Int) (digits : List Int) : Prop :=
  Zlength digits = n ∧ Forall (fun d => 1 ≤ d ∧ d ≤ 9) digits ∧
  DecimalValue digits > 0 ∧ Forall (fun d => ¬ Z.divide d (DecimalValue digits)) digits

def Pre (n : Int) : Prop := 1 ≤ n ∧ n ≤ 100000

def Spec (n : Int) (out : Option (List Int)) : Prop :=
  (∃ digits, out = some digits ∧ BadUglyDigits n digits) ∨
  (out = none ∧ ∀ digits, ¬ BadUglyDigits n digits)

end Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers.lean
