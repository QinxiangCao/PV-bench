import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.annoying_math_homework.lean

open AUXLib SimpleC.SL.IntLib

def digit_sum_modulus : Int := 1000000007

inductive Base10DigitSum : Int → Int → Prop where
  | Base10DigitSum_zero : Base10DigitSum 0 0
  | Base10DigitSum_positive (n quotient quotient_sum : Int) :
      0 < n → quotient = Z.div n 10 → Base10DigitSum quotient quotient_sum →
      Base10DigitSum n (quotient_sum + Z.modulo n 10)

export Base10DigitSum (Base10DigitSum_zero Base10DigitSum_positive)

inductive InclusiveDigitSum (lo : Int) : Int → Int → Prop where
  | InclusiveDigitSum_single (digit_sum : Int) : Base10DigitSum lo digit_sum → InclusiveDigitSum lo lo digit_sum
  | InclusiveDigitSum_extend (hi total next_digit_sum : Int) :
      lo ≤ hi → InclusiveDigitSum lo hi total → Base10DigitSum (hi+1) next_digit_sum →
      InclusiveDigitSum lo (hi+1) (total+next_digit_sum)

@[match_pattern] abbrev InclusiveDigitSum_single (lo digit_sum : Int) (h : Base10DigitSum lo digit_sum) :=
  InclusiveDigitSum.InclusiveDigitSum_single (lo := lo) digit_sum h

@[match_pattern] abbrev InclusiveDigitSum_extend (lo hi total next_digit_sum : Int) (hh : lo ≤ hi)
    (h : InclusiveDigitSum lo hi total) (hn : Base10DigitSum (hi+1) next_digit_sum) :=
  InclusiveDigitSum.InclusiveDigitSum_extend (lo := lo) hi total next_digit_sum hh h hn

def IntervalDigitSum (lo hi answer : Int) : Prop :=
  ∃ total, lo ≤ hi ∧ InclusiveDigitSum lo hi total ∧ answer = Z.modulo total digit_sum_modulus

def PowerTable (power : List Int) : Prop :=
  Zlength power = 20 ∧ ∀ i, (0 ≤ i ∧ i < 20) → Znth i power 0 = Z.modulo (Z.pow 10 i) digit_sum_modulus

def DigitDPValue (places leading : Int) : Int :=
  if places = 1 then Z.modulo leading digit_sum_modulus else
    Z.modulo (leading * Z.pow 10 (places-1) + 45 * (places-1) * Z.pow 10 (places-2)) digit_sum_modulus

def DigitDPTable (dp : List Int) : Prop :=
  Zlength dp = 200 ∧ (∀ j, (0 ≤ j ∧ j < 10) → Znth j dp 0 = 0) ∧
  ∀ places leading, (1 ≤ places ∧ places < 20) → (0 ≤ leading ∧ leading < 10) →
    Znth (places*10+leading) dp 0 = DigitDPValue places leading

end Algorithms.annoying_math_homework.lean
