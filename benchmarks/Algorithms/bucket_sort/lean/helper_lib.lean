import AUXLib.Sorting
import SimpleC.SL.SeparationLogic

namespace Algorithms.bucket_sort.lean

open AUXLib
abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none
abbrev _App_option_Z := Option Int

def RadixDigit (value exponent : Int) : Int := Z.modulo (Z.div value exponent) 10

def PrefixMaximum (values : List Int) (hi maximum : Int) : Prop :=
  (∃ index, (0 ≤ index ∧ index < hi) ∧ maximum = Znth index values 0) ∧
  ∀ index, (0 ≤ index ∧ index < hi) → Znth index values 0 ≤ maximum

def DecimalExponent (exponent : Int) : Prop :=
  ∃ power : Int, (0 ≤ power ∧ power ≤ 9) ∧ exponent = Z.pow 10 power

def RadixLowerDigitsOrdered (values : List Int) (exponent : Int) : Prop :=
  ∀ left right, (0 ≤ left ∧ left ≤ right ∧ right < Zlength values) →
    Z.modulo (Znth left values 0) exponent ≤ Z.modulo (Znth right values 0) exponent

def RadixPassState (input current : List Int) (exponent : Int) : Prop :=
  Permutation input current ∧ RadixLowerDigitsOrdered current exponent

def RadixBucket (values : List Int) (exponent digit : Int) : List Int :=
  values.filter (fun value => decide (RadixDigit value exponent = digit))

def RadixDigitCount (values : List Int) (exponent hi digit : Int) : Int :=
  Zlength (RadixBucket (sublist 0 hi values) exponent digit)

def DigitHistogramPrefix (values : List Int) (exponent hi : Int) (counts : List Int) : Prop :=
  ∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit counts 0 = RadixDigitCount values exponent hi digit

def DigitPrefixTotals (histogram totals : List Int) (processed : Int) : Prop :=
  ∀ digit, (0 ≤ digit ∧ digit < 10) →
    (digit < processed → Znth digit totals 0 = sum (sublist 0 (digit + 1) histogram)) ∧
    (processed ≤ digit → Znth digit totals 0 = Znth digit histogram 0)

def RadixBucketStart (histogram : List Int) (digit : Int) : Int := sum (sublist 0 digit histogram)

def RadixBucketEnd (histogram : List Int) (digit : Int) : Int := sum (sublist 0 (digit + 1) histogram)

def RadixStableOutput (source : List Int) (exponent : Int) : List Int :=
  ([0,1,2,3,4,5,6,7,8,9].map (fun digit => RadixBucket source exponent digit)).flatten

def StableDigitPass (source output : List Int) (exponent : Int) : Prop := output = RadixStableOutput source exponent

def BucketPlacementProgress (source : List Int) (exponent remaining : Int) (histogram counters : List Int)
    (mixed_output : List (Option Int)) : Prop :=
  Zlength mixed_output = 1000 ∧
  (∀ digit, (0 ≤ digit ∧ digit < 10) → Znth digit counters 0 = RadixBucketStart histogram digit + RadixDigitCount source exponent remaining digit) ∧
  (∀ digit, (0 ≤ digit ∧ digit < 10) → RadixBucketStart histogram digit ≤ Znth digit counters 0 ∧ Znth digit counters 0 ≤ RadixBucketEnd histogram digit) ∧
  (∀ digit position, (0 ≤ digit ∧ digit < 10) → (Znth digit counters 0 ≤ position ∧ position < RadixBucketEnd histogram digit) →
    Znth position mixed_output none = some (Znth position (RadixStableOutput source exponent) 0)) ∧
  (∀ position, (0 ≤ position ∧ position < 1000) →
    (∀ digit, (0 ≤ digit ∧ digit < 10) → position < Znth digit counters 0 ∨ RadixBucketEnd histogram digit ≤ position) →
    Znth position mixed_output none = none)

def RadixCopyPrefix (source pass_output working : List Int) (copied : Int) : Prop :=
  (∀ index, (0 ≤ index ∧ index < copied) → Znth index working 0 = Znth index pass_output 0) ∧
  (∀ index, (copied ≤ index ∧ index < Zlength source) → Znth index working 0 = Znth index source 0)

end Algorithms.bucket_sort.lean
