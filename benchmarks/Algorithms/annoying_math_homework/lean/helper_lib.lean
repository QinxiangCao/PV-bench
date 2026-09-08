import Algorithms.annoying_math_homework.lean.spec_lib

namespace Algorithms.annoying_math_homework.lean

open AUXLib SimpleC.SL.IntLib

inductive PrefixDigitSum : Int → Int → Prop where
  | PrefixDigitSum_nonpositive (x : Int) : x ≤ 0 → PrefixDigitSum x 0
  | PrefixDigitSum_positive_base : PrefixDigitSum 1 1
  | PrefixDigitSum_positive_step (x total next_digit_sum : Int) :
      1 ≤ x → PrefixDigitSum x total → Base10DigitSum (x+1) next_digit_sum →
      PrefixDigitSum (x+1) (Z.modulo (total + next_digit_sum) digit_sum_modulus)

export PrefixDigitSum (PrefixDigitSum_nonpositive PrefixDigitSum_positive_base PrefixDigitSum_positive_step)

def PowerPrefix (power : List Int) (hi : Int) : Prop :=
  Zlength power = hi ∧ (1 ≤ hi ∧ hi ≤ 20) ∧
  ∀ i, (0 ≤ i ∧ i < hi) → Znth i power 0 = Z.modulo (Z.pow 10 i) digit_sum_modulus

def ZeroSegment (values : List Int) (hi total : Int) : Prop :=
  Zlength values = hi ∧ (0 ≤ hi ∧ hi ≤ total) ∧ ∀ k, (0 ≤ k ∧ k < hi) → Znth k values 0 = 0

def DigitDPBaseProgress (dp : List Int) (next : Int) : Prop :=
  Zlength dp = 200 ∧ (0 ≤ next ∧ next ≤ 10) ∧
  (∀ j, (0 ≤ j ∧ j < next) → Znth (10+j) dp 0 = j) ∧
  ∀ k, (0 ≤ k ∧ k < 200) → (k < 10 ∨ 20 ≤ k ∨ 10+next ≤ k) → Znth k dp 0 = 0

def DigitDPOuterProgress (dp : List Int) (next_places : Int) : Prop :=
  Zlength dp = 200 ∧ (2 ≤ next_places ∧ next_places ≤ 20) ∧
  (∀ d, (0 ≤ d ∧ d < 10) → Znth d dp 0 = 0) ∧
  (∀ places leading, (1 ≤ places ∧ places < next_places) → (0 ≤ leading ∧ leading < 10) →
    Znth (places*10+leading) dp 0 = DigitDPValue places leading) ∧
  ∀ places leading, (next_places ≤ places ∧ places < 20) → (0 ≤ leading ∧ leading < 10) →
    Znth (places*10+leading) dp 0 = 0

def DigitDPRowProgress (dp : List Int) (places next_leading : Int) : Prop :=
  Zlength dp = 200 ∧ (2 ≤ places ∧ places < 20) ∧ (0 ≤ next_leading ∧ next_leading ≤ 10) ∧
  (∀ d, (0 ≤ d ∧ d < 10) → Znth d dp 0 = 0) ∧
  (∀ p d, (1 ≤ p ∧ p < places) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = DigitDPValue p d) ∧
  (∀ d, (0 ≤ d ∧ d < next_leading) → Znth (places*10+d) dp 0 = DigitDPValue places d) ∧
  (∀ d, (next_leading ≤ d ∧ d < 10) → Znth (places*10+d) dp 0 = 0) ∧
  ∀ p d, (places < p ∧ p < 20) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = 0

inductive InnerCandidateDigitSum (dp : List Int) (places : Int) : Int → Int → Prop where
  | InnerCandidateDigitSum_zero : InnerCandidateDigitSum dp places 0 0
  | InnerCandidateDigitSum_step (next «partial» : Int) :
      0 ≤ next → InnerCandidateDigitSum dp places next «partial» →
      InnerCandidateDigitSum dp places (next+1)
        (Z.modulo («partial» + Znth (places*10+next) dp 0) digit_sum_modulus)

@[match_pattern] abbrev InnerCandidateDigitSum_zero (dp : List Int) (places : Int) :=
  InnerCandidateDigitSum.InnerCandidateDigitSum_zero (dp := dp) (places := places)

@[match_pattern] abbrev InnerCandidateDigitSum_step (dp : List Int) (places next «partial» : Int)
    (hn : 0 ≤ next) (h : InnerCandidateDigitSum dp places next «partial») :=
  InnerCandidateDigitSum.InnerCandidateDigitSum_step (dp := dp) (places := places) next «partial» hn h

def DigitDPCellProgress (dp : List Int) (places leading next_suffix : Int) : Prop :=
  Zlength dp = 200 ∧ (2 ≤ places ∧ places < 20) ∧ (0 ≤ leading ∧ leading < 10) ∧
  (0 ≤ next_suffix ∧ next_suffix ≤ 10) ∧
  (∀ d, (0 ≤ d ∧ d < 10) → Znth d dp 0 = 0) ∧
  (∀ p d, (1 ≤ p ∧ p < places) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = DigitDPValue p d) ∧
  (∀ d, (0 ≤ d ∧ d < leading) → Znth (places*10+d) dp 0 = DigitDPValue places d) ∧
  (∀ d, (leading < d ∧ d < 10) → Znth (places*10+d) dp 0 = 0) ∧
  (∀ p d, (places < p ∧ p < 20) → (0 ≤ d ∧ d < 10) → Znth (p*10+d) dp 0 = 0) ∧
  ∃ «partial», InnerCandidateDigitSum dp (places-1) next_suffix «partial» ∧
    Znth (places*10+leading) dp 0 = Z.modulo («partial» + next_suffix * Z.pow 10 (places-2) * leading) digit_sum_modulus

def ExtractedDigitBuffer (x : Int) (digits : List Int) (count remaining : Int) : Prop :=
  Zlength digits = 20 ∧ (0 ≤ count ∧ count ≤ 19) ∧ remaining = Z.div x (Z.pow 10 count) ∧
  (∀ k, (1 ≤ k ∧ k ≤ count) → Znth k digits 0 = Z.modulo (Z.div x (Z.pow 10 (k-1))) 10) ∧
  ∀ k, (count < k ∧ k < 20) → Znth k digits 0 = 0

def ExtractedDigitCount (x count : Int) : Prop :=
  (1 ≤ count ∧ count ≤ 19) ∧ (Z.pow 10 (count-1) ≤ x ∧ x < Z.pow 10 count)

def DigitPositionPower (position power : Int) : Prop :=
  (1 ≤ position ∧ position ≤ 19) ∧ power = Z.pow 10 (position-1)

def OuterDigitPositionPower (position power : Int) : Prop :=
  (position = 0 ∧ power = 0) ∨ ((1 ≤ position ∧ position ≤ 19) ∧ power = Z.pow 10 (position-1))

def AccumulatedDigitSumCorrect (x position answer : Int) : Prop :=
  (position = 0 ∧ PrefixDigitSum x answer) ∨
  (1 ≤ position ∧ ∃ high high_digit_sum before, high = Z.div x (Z.pow 10 position) ∧
    Base10DigitSum high high_digit_sum ∧ PrefixDigitSum (high-1) before ∧
    answer = Z.modulo (Z.pow 10 position * before + 45 * high * position * Z.pow 10 (position-1) +
      (Z.modulo x (Z.pow 10 position)+1)*high_digit_sum) digit_sum_modulus)

inductive DigitPositionAccumulation (x : Int) (dp digits : List Int) : Int → Int → Prop where
  | DigitPositionAccumulation_start (count : Int) :
      ExtractedDigitBuffer x digits count 0 → ExtractedDigitCount x count →
      DigitPositionAccumulation x dp digits count 0
  | DigitPositionAccumulation_step (places answer choice_sum : Int) :
      1 ≤ places → DigitPositionAccumulation x dp digits places answer →
      InnerCandidateDigitSum dp places (Znth places digits 0) choice_sum →
      DigitPositionAccumulation x dp digits (places-1)
        (Z.modulo (answer + choice_sum + Z.modulo (Z.modulo x (Z.pow 10 (places-1))+1) digit_sum_modulus *
          Znth places digits 0) digit_sum_modulus)

@[match_pattern] abbrev DigitPositionAccumulation_start (x : Int) (dp digits : List Int) (count : Int)
    (hb : ExtractedDigitBuffer x digits count 0) (hc : ExtractedDigitCount x count) :=
  DigitPositionAccumulation.DigitPositionAccumulation_start (x := x) (dp := dp) (digits := digits) count hb hc

@[match_pattern] abbrev DigitPositionAccumulation_step (x : Int) (dp digits : List Int) (places answer choice_sum : Int)
    (hp : 1 ≤ places) (h : DigitPositionAccumulation x dp digits places answer)
    (hs : InnerCandidateDigitSum dp places (Znth places digits 0) choice_sum) :=
  DigitPositionAccumulation.DigitPositionAccumulation_step (x := x) (dp := dp) (digits := digits) places answer choice_sum hp h hs

def OuterDigitPositionProgress (x : Int) (dp digits : List Int) (position answer : Int) : Prop :=
  DigitPositionAccumulation x dp digits position answer

def InnerCandidateDigitProgress (x : Int) (dp digits : List Int) (places next_digit answer_before answer : Int) : Prop :=
  (1 ≤ places ∧ places ≤ 19) ∧ (0 ≤ next_digit ∧ next_digit ≤ Znth places digits 0) ∧
  OuterDigitPositionProgress x dp digits places answer_before ∧ ∃ choice_sum,
    InnerCandidateDigitSum dp places next_digit choice_sum ∧ answer = Z.modulo (answer_before + choice_sum) digit_sum_modulus

end Algorithms.annoying_math_homework.lean
