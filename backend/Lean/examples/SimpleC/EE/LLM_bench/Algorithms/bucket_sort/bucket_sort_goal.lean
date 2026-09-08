import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bucket_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def sort_safety_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  ((( &( "max_value" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "max_value" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "max_value" ) )) # Int |-> ((Znth i input (0 : Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  ((( &( "exponent" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "count" ) ) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** (intArray.full a_pre n_pre input)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 1000000000)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input n_pre max_value)) (PreH12 : (DecimalExponent exponent)) (PreH13 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ ((max_value ≠ (INT_MIN)) ∨ (exponent ≠ (-1))) ” &&
  “ (exponent ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 1000000000)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input n_pre max_value)) (PreH12 : (DecimalExponent exponent)) (PreH13 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current exponent)) ,
  ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_10 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit : Int) (zero_prefix : (List Int)) (current : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (zero_prefix)) = digit)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : ((0 : Int) <= digit)) (PreH12 : (digit <= 10)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH14 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) ((0 : Int))) = (0 : Int)))) (PreH16 : (PrefixMaximum input n_pre max_value)) (PreH17 : (DecimalExponent exponent)) (PreH18 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_11 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit : Int) (zero_prefix : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_12 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit : Int) (zero_prefix : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) ,
  (intArray.seg ( &( "count" ) ) (0 : Int) (digit + 1) (zero_prefix ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((digit + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (digit + 1)) ”

noncomputable def sort_safety_wit_13 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (counts)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> ((Znth (digit) (counts) ((0 : Int))) = (0 : Int)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent (0 : Int) counts)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_14 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Z.quot (Znth i current (0 : Int)) exponent) ≠ (INT_MIN)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_15 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth i current (0 : Int)) ≠ (INT_MIN)) ∨ (exponent ≠ (-1))) ” &&
  “ (exponent ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_16 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_17 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int)) + 1)) ”
) \/
(
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int)) + 1)) ”
)

noncomputable def sort_safety_wit_17_split_goal_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int)) + 1) <= INT_MAX) ”

noncomputable def sort_safety_wit_17_split_goal_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((INT_MIN) <= ((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int)) + 1)) ”

noncomputable def sort_safety_wit_18 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int)) + 1)) (counts)))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_19 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent n_pre histogram)) ,
  ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 histogram)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_20 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (totals)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : (1 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_21 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) ”
)

noncomputable def sort_safety_wit_21_split_goal_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int))) <= INT_MAX) ”

noncomputable def sort_safety_wit_21_split_goal_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((INT_MIN) <= ((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) ”

noncomputable def sort_safety_wit_22 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((digit - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (digit - 1)) ”

noncomputable def sort_safety_wit_23 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_24 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) (totals)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((digit + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (digit + 1)) ”

noncomputable def sort_safety_wit_25 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (endpoints : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH14 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (endpoints) ((0 : Int))))) ∧ ((Znth (digit) (endpoints) ((0 : Int))) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH19 : (DigitPrefixTotals histogram endpoints 10)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 endpoints)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def sort_safety_wit_26 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (endpoints : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH14 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (endpoints) ((0 : Int))))) ∧ ((Znth (digit) (endpoints) ((0 : Int))) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH19 : (DigitPrefixTotals histogram endpoints 10)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 endpoints)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_27 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (counters : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (counters)) = 10)) (PreH7 : ((Zlength (mixed_output)) = 1000)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : ((-1) <= i)) (PreH14 : (i < n_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH17 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_28 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH18 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value)) (PreH21 : (DecimalExponent exponent)) (PreH22 : (RadixPassState input current exponent)) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH24 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (((Z.quot (Znth i current (0 : Int)) exponent) ≠ (INT_MIN)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_29 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH18 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value)) (PreH21 : (DecimalExponent exponent)) (PreH22 : (RadixPassState input current exponent)) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH24 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (((Znth i current (0 : Int)) ≠ (INT_MIN)) ∨ (exponent ≠ (-1))) ” &&
  “ (exponent ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_30 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH18 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value)) (PreH21 : (DecimalExponent exponent)) (PreH22 : (RadixPassState input current exponent)) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH24 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_31 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH3 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH4 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (max_value >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : ((Zlength (input)) = n_pre)) (PreH13 : ((Zlength (current)) = n_pre)) (PreH14 : ((Zlength (histogram)) = 10)) (PreH15 : ((Zlength (counters)) = 10)) (PreH16 : ((Zlength (mixed_output)) = 1000)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((-1) <= i)) (PreH23 : (i < n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH27 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH28 : (PrefixMaximum input n_pre max_value)) (PreH29 : (DecimalExponent exponent)) (PreH30 : (RadixPassState input current exponent)) (PreH31 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH32 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full ( &( "count" ) ) 10 counters)
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) ”

noncomputable def sort_safety_wit_32 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))))) (PreH2 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current exponent)) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH38 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth ((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)) (0 : Int))) ((Some ((Znth i current (0 : Int))))) (mixed_output)))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def sort_safety_wit_33 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (bucket_starts : (List Int)) (pass_output : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH14 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)))) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH19 : (StableDigitPass current pass_output exponent)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_34 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working) ((0 : Int))))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output exponent)) (PreH22 : (RadixCopyPrefix current pass_output working i)) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - (0 : Int)) pass_output (0 : Int))) (working)))
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_35 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (pass_output : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10))) (PreH10 : ((exponent * 10) <= 1000000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int)))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent (exponent * 10))) (PreH16 : (RadixPassState input pass_output (exponent * 10))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre pass_output)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ ((exponent * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (exponent * 10)) ”

noncomputable def sort_safety_wit_36 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (pass_output : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10))) (PreH10 : ((exponent * 10) <= 1000000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int)))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent (exponent * 10))) (PreH16 : (RadixPassState input pass_output (exponent * 10))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre pass_output)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  (intArray.full a_pre n_pre input)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) input (0 : Int))) ” &&
  “ ((Znth (0 : Int) input (0 : Int)) <= 999999999) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input 1 (Znth (0 : Int) input (0 : Int))) ”
  &&  (intArray.full a_pre n_pre input)
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  TT && emp 
|--
  “ (PrefixMaximum input 1 (Znth (0 : Int) input (0 : Int))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ ((Znth (0 : Int) input (0 : Int)) <= 999999999) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) input (0 : Int))) ”
  &&  emp
)

noncomputable def sort_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  (PrefixMaximum input 1 (Znth (0 : Int) input (0 : Int)))

noncomputable def sort_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  ((Znth (0 : Int) input (0 : Int)) <= 999999999)

noncomputable def sort_entail_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  ((0 : Int) <= (Znth (0 : Int) input (0 : Int)))

noncomputable def sort_entail_wit_2_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) <= 999999999) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input (i + 1) (Znth i input (0 : Int))) ”
  &&  (intArray.full a_pre n_pre input)
) \/
(
forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1) (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) <= 999999999) ”
  &&  emp
)

noncomputable def sort_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  (PrefixMaximum input (i + 1) (Znth i input (0 : Int)))

noncomputable def sort_entail_wit_2_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  ((Znth i input (0 : Int)) <= 999999999)

noncomputable def sort_entail_wit_2_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input (i + 1) max_value) ”
  &&  (intArray.full a_pre n_pre input)
) \/
(
forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1) max_value) ”
  &&  emp
)

noncomputable def sort_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  (PrefixMaximum input (i + 1) max_value)

noncomputable def sort_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  (intArray.undef_full ( &( "count" ) ) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.full a_pre n_pre input)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 1000000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent 1) ” &&
  “ (RadixPassState input current 1) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
) \/
(
forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  TT && emp 
|--
  “ (RadixPassState input input 1) ” &&
  “ (DecimalExponent 1) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (input) ((0 : Int)))) ∧ ((Znth (k_2) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ”
  &&  emp
)

noncomputable def sort_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  (RadixPassState input input 1)

noncomputable def sort_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  (DecimalExponent 1)

noncomputable def sort_entail_wit_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  (PrefixMaximum input n_pre max_value)

noncomputable def sort_entail_wit_3_split_goal_4 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (input) ((0 : Int)))) ∧ ((Znth (k_2) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_3_split_goal_5 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current_2 exponent)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  EX zero_prefix : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (zero_prefix)) = (0 : Int)) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth (k_3) (zero_prefix) ((0 : Int))) = (0 : Int))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) (0 : Int) zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) (0 : Int) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current_2 exponent)) ,
  TT && emp 
|--
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth (k_3) ((@List.nil Int)) ((0 : Int))) = (0 : Int))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def sort_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current_2 exponent)) ,
  forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth (k_3) ((@List.nil Int)) ((0 : Int))) = (0 : Int)))

noncomputable def sort_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current_2 exponent)) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_4_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current_2 exponent)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_4_split_goal_4 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current_2 exponent)) ,
  (exponent <= 100000000)

noncomputable def sort_entail_wit_4_split_goal_5 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current_2 exponent)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def sort_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit : Int) (zero_prefix_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix_2)) = digit)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix_2) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) ,
  (intArray.seg ( &( "count" ) ) (0 : Int) (digit + 1) (zero_prefix_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX zero_prefix : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (zero_prefix)) = (digit + 1)) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (digit + 1)) ” &&
  “ ((digit + 1) <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (digit + 1))) -> ((Znth (k_3) (zero_prefix) ((0 : Int))) = (0 : Int))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) (digit + 1) zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit : Int) (zero_prefix_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix_2)) = digit)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix_2) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) ,
  TT && emp 
|--
  “ ((Zlength ((zero_prefix_2 ++ ((0 : Int) :: (@List.nil Int))))) = (digit + 1)) ”
  &&  emp
)

noncomputable def sort_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit : Int) (zero_prefix_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix_2)) = digit)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix_2) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) ,
  ((Zlength ((zero_prefix_2 ++ ((0 : Int) :: (@List.nil Int))))) = (digit + 1))

noncomputable def sort_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit_2 : Int) (zero_prefix : (List Int)) (current_2 : (List Int)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit_2)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit_2)) (PreH13 : (digit_2 <= 10)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < digit_2)) -> ((Znth (k_5) (zero_prefix) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit_2 zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit_2 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX counts : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> ((Znth (digit) (counts) ((0 : Int))) = (0 : Int))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent (0 : Int) counts) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit_2 : Int) (zero_prefix : (List Int)) (current_2 : (List Int)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit_2)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit_2)) (PreH13 : (digit_2 <= 10)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < digit_2)) -> ((Znth (k_5) (zero_prefix) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) ,
  (intArray.seg ( &( "count" ) ) (0 : Int) digit_2 zero_prefix)
|--
  EX counts : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current_2)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> ((Znth (digit) (counts) ((0 : Int))) = (0 : Int))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current_2 exponent) ” &&
  “ (DigitHistogramPrefix current_2 exponent (0 : Int) counts) ”
  &&  (intArray.full ( &( "count" ) ) 10 counts)
)

noncomputable def sort_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) ((0 : Int))) = (0 : Int)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent (0 : Int) counts_2)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 counts_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX counts : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= (0 : Int)))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent (0 : Int) counts) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) ((0 : Int))) = (0 : Int)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent (0 : Int) counts_2)) ,
  TT && emp 
|--
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts_2) ((0 : Int)))) ∧ ((Znth (digit) (counts_2) ((0 : Int))) <= (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ”
  &&  emp
)

noncomputable def sort_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) ((0 : Int))) = (0 : Int)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent (0 : Int) counts_2)) ,
  forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts_2) ((0 : Int)))) ∧ ((Znth (digit) (counts_2) ((0 : Int))) <= (0 : Int))))

noncomputable def sort_entail_wit_7_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) ((0 : Int))) = (0 : Int)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent (0 : Int) counts_2)) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_7_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) ((0 : Int))) = (0 : Int)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent (0 : Int) counts_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ” &&
  “ (i <= INT_MAX) ” &&
  “ (exponent <= INT_MAX) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (exponent >= INT_MIN) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent i counts) ”
  &&  ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  TT && emp 
|--
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ”
  &&  emp
)

noncomputable def sort_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)

noncomputable def sort_entail_wit_8_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))

noncomputable def sort_entail_wit_9 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts_2 : (List Int)) (current_2 : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts_2) ((0 : Int)))) ∧ ((Znth (digit) (counts_2) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current_2 exponent)) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) counts_2 (0 : Int)) + 1)) (counts_2)))
  ** (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX counts : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= (i + 1)))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent (i + 1) counts) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts_2 : (List Int)) (current_2 : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts_2) ((0 : Int)))) ∧ ((Znth (digit) (counts_2) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current_2 exponent)) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2)) ,
  TT && emp 
|--
  “ (DigitHistogramPrefix current_2 exponent (i + 1) (replace_Znth ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) counts_2 (0 : Int)) + 1)) (counts_2))) ” &&
  “ ((Zlength ((replace_Znth ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) counts_2 (0 : Int)) + 1)) (counts_2)))) = 10) ”
  &&  emp
)

noncomputable def sort_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts_2 : (List Int)) (current_2 : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts_2) ((0 : Int)))) ∧ ((Znth (digit) (counts_2) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current_2 exponent)) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2)) ,
  (DigitHistogramPrefix current_2 exponent (i + 1) (replace_Znth ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) counts_2 (0 : Int)) + 1)) (counts_2)))

noncomputable def sort_entail_wit_9_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts_2 : (List Int)) (current_2 : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts_2) ((0 : Int)))) ∧ ((Znth (digit) (counts_2) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current_2 exponent)) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2)) ,
  ((Zlength ((replace_Znth ((Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth i current_2 (0 : Int)) exponent) 10) counts_2 (0 : Int)) + 1)) (counts_2)))) = 10)

noncomputable def sort_entail_wit_10 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((0 : Int) <= (Znth (digit_2) (counts) ((0 : Int)))) ∧ ((Znth (digit_2) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX histogram : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 histogram)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((0 : Int) <= (Znth (digit_2) (counts) ((0 : Int)))) ∧ ((Znth (digit_2) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  TT && emp 
|--
  “ (DigitHistogramPrefix current_2 exponent n_pre counts) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ”
  &&  emp
)

noncomputable def sort_entail_wit_10_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((0 : Int) <= (Znth (digit_2) (counts) ((0 : Int)))) ∧ ((Znth (digit_2) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  (DigitHistogramPrefix current_2 exponent n_pre counts)

noncomputable def sort_entail_wit_10_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((0 : Int) <= (Znth (digit_2) (counts) ((0 : Int)))) ∧ ((Znth (digit_2) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= n_pre)))

noncomputable def sort_entail_wit_10_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((0 : Int) <= (Znth (digit_2) (counts) ((0 : Int)))) ∧ ((Znth (digit_2) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_10_split_goal_4 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((0 : Int) <= (Znth (digit_2) (counts) ((0 : Int)))) ∧ ((Znth (digit_2) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_11 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (input) ((0 : Int)))) ∧ ((Znth (k_5) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> (((0 : Int) <= (Znth (k_6) (current_2) ((0 : Int)))) ∧ ((Znth (k_6) (current_2) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit) (histogram_2) ((0 : Int))) <= n_pre)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 histogram_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX totals : (List Int), EX histogram : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (totals)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals 1) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : ((0 : Int) < (Z.quot max_value exponent))) (PreH11 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (input) ((0 : Int)))) ∧ ((Znth (k_5) (input) ((0 : Int))) <= 999999999)))) (PreH12 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> (((0 : Int) <= (Znth (k_6) (current_2) ((0 : Int)))) ∧ ((Znth (k_6) (current_2) ((0 : Int))) <= 999999999)))) (PreH13 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit) (histogram_2) ((0 : Int))) <= n_pre)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) ,
  TT && emp 
|--
  EX histogram : (List Int),
  “ ((Zlength (histogram)) = 10) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 10) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= (Zlength (input))))) ” &&
  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram) ” &&
  “ (DigitPrefixTotals histogram histogram_2 1) ”
  &&  emp
)

noncomputable def sort_entail_wit_12 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals_2 : (List Int)) (histogram_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals_2)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram_2) ((0 : Int)))) ∧ ((Znth (k_3) (histogram_2) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals_2) ((0 : Int)))) ∧ ((Znth (k_4) (totals_2) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current_2 exponent)) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH23 : (DigitPrefixTotals histogram_2 totals_2 digit)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2)))
  ** (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX totals : (List Int), EX histogram : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (totals)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= (digit + 1)) ” &&
  “ ((digit + 1) <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals (digit + 1)) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals_2 : (List Int)) (histogram_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals_2)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram_2) ((0 : Int)))) ∧ ((Znth (k_3) (histogram_2) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals_2) ((0 : Int)))) ∧ ((Znth (k_4) (totals_2) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current_2 exponent)) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH23 : (DigitPrefixTotals histogram_2 totals_2 digit)) ,
  TT && emp 
|--
  EX histogram : (List Int),
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength ((replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2)))) = 10) ” &&
  “ (1 <= (digit + 1)) ” &&
  “ ((digit + 1) <= 10) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= (Zlength (input))))) ” &&
  “ forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) ((replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2))) ((0 : Int)))) ∧ ((Znth (k_4) ((replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2))) ((0 : Int))) <= (Zlength (input))))) ” &&
  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram) ” &&
  “ (DigitPrefixTotals histogram (replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2)) (digit + 1)) ”
  &&  emp
)

noncomputable def sort_entail_wit_13 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit_2 : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit_2)) (PreH14 : (digit_2 <= 10)) (PreH15 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < 10)) -> (((0 : Int) <= (Znth (k_5) (histogram_2) ((0 : Int)))) ∧ ((Znth (k_5) (histogram_2) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < 10)) -> (((0 : Int) <= (Znth (k_6) (totals) ((0 : Int)))) ∧ ((Znth (k_6) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current_2 exponent)) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH23 : (DigitPrefixTotals histogram_2 totals digit_2)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX endpoints : (List Int), EX histogram : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (endpoints)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (endpoints) ((0 : Int))))) ∧ ((Znth (digit) (endpoints) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram endpoints 10) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 endpoints)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (digit_2 : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit_2)) (PreH14 : (digit_2 <= 10)) (PreH15 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < 10)) -> (((0 : Int) <= (Znth (k_5) (histogram_2) ((0 : Int)))) ∧ ((Znth (k_5) (histogram_2) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < 10)) -> (((0 : Int) <= (Znth (k_6) (totals) ((0 : Int)))) ∧ ((Znth (k_6) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current_2 exponent)) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH23 : (DigitPrefixTotals histogram_2 totals digit_2)) ,
  TT && emp 
|--
  EX histogram : (List Int),
  “ ((Zlength (histogram)) = 10) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= (Zlength (input)))) ∧ ((0 : Int) <= (Znth (digit) (totals) ((0 : Int))))) ∧ ((Znth (digit) (totals) ((0 : Int))) <= (Zlength (input))))) ” &&
  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram) ” &&
  “ (DigitPrefixTotals histogram totals 10) ”
  &&  emp
)

noncomputable def sort_entail_wit_14 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram_2 : (List Int)) (endpoints : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH14 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((((0 : Int) <= (Znth (digit_2) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit_2) (histogram_2) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit_2) (endpoints) ((0 : Int))))) ∧ ((Znth (digit_2) (endpoints) ((0 : Int))) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current_2 exponent)) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH19 : (DigitPrefixTotals histogram_2 endpoints 10)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 endpoints)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX mixed_output : (List (Option Int)), EX counters : (List Int), EX histogram : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= (n_pre - 1))) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent ((n_pre - 1) + 1) histogram counters mixed_output) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram_2 : (List Int)) (endpoints : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (input) ((0 : Int)))) ∧ ((Znth (k_4) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> (((0 : Int) <= (Znth (k_5) (current_2) ((0 : Int)))) ∧ ((Znth (k_5) (current_2) ((0 : Int))) <= 999999999)))) (PreH14 : forall (digit_2 : Int) , ((((0 : Int) <= digit_2) ∧ (digit_2 < 10)) -> (((((0 : Int) <= (Znth (digit_2) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit_2) (histogram_2) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit_2) (endpoints) ((0 : Int))))) ∧ ((Znth (digit_2) (endpoints) ((0 : Int))) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current_2 exponent)) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH19 : (DigitPrefixTotals histogram_2 endpoints 10)) ,
  (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX mixed_output : (List (Option Int)), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current_2)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (endpoints)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current_2) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current_2) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (endpoints) ((0 : Int))))) ∧ ((Znth (digit) (endpoints) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= (n_pre - 1))) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) (endpoints) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) (endpoints) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current_2 exponent) ” &&
  “ (DigitHistogramPrefix current_2 exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current_2 exponent ((n_pre - 1) + 1) histogram endpoints mixed_output) ”
  &&  (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
)

noncomputable def sort_entail_wit_15 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH18 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value)) (PreH21 : (DecimalExponent exponent)) (PreH22 : (RadixPassState input current exponent)) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH24 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : ((0 : Int) <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : ((0 : Int) < (Z.quot max_value exponent))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH27 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH28 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH29 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value)) (PreH31 : (DecimalExponent exponent)) (PreH32 : (RadixPassState input current exponent)) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH34 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  TT && emp 
|--
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ”
  &&  emp
)

noncomputable def sort_entail_wit_15_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : ((0 : Int) <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : ((0 : Int) < (Z.quot max_value exponent))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH27 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH28 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH29 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value)) (PreH31 : (DecimalExponent exponent)) (PreH32 : (RadixPassState input current exponent)) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH34 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)

noncomputable def sort_entail_wit_15_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : ((0 : Int) <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : ((0 : Int) < (Z.quot max_value exponent))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH27 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH28 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH29 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value)) (PreH31 : (DecimalExponent exponent)) (PreH32 : (RadixPassState input current exponent)) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH34 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))

noncomputable def sort_entail_wit_15_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : ((0 : Int) <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : ((0 : Int) < (Z.quot max_value exponent))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH27 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH28 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH29 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value)) (PreH31 : (DecimalExponent exponent)) (PreH32 : (RadixPassState input current exponent)) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH34 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)

noncomputable def sort_entail_wit_15_split_goal_4 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : ((0 : Int) <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : ((0 : Int) < (Z.quot max_value exponent))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH27 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH28 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH29 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value)) (PreH31 : (DecimalExponent exponent)) (PreH32 : (RadixPassState input current exponent)) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH34 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))

noncomputable def sort_entail_wit_16 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH3 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH4 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (max_value >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : ((Zlength (input)) = n_pre)) (PreH13 : ((Zlength (current)) = n_pre)) (PreH14 : ((Zlength (histogram)) = 10)) (PreH15 : ((Zlength (counters)) = 10)) (PreH16 : ((Zlength (mixed_output)) = 1000)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((-1) <= i)) (PreH23 : (i < n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH27 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH28 : (PrefixMaximum input n_pre max_value)) (PreH29 : (DecimalExponent exponent)) (PreH30 : (RadixPassState input current exponent)) (PreH31 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH32 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000) ” &&
  “ (exponent <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (exponent >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  ((( &( "digit" ) )) # Int |-> ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)))
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (exponent <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) <= INT_MAX)) (PreH4 : (exponent >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current exponent)) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH38 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  TT && emp 
|--
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000) ” &&
  “ ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int)))) ”
  &&  emp
)

noncomputable def sort_entail_wit_16_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (exponent <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) <= INT_MAX)) (PreH4 : (exponent >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current exponent)) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH38 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000)

noncomputable def sort_entail_wit_16_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (exponent <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) <= INT_MAX)) (PreH4 : (exponent >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current exponent)) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH38 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))))

noncomputable def sort_entail_wit_17 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output_2 : (List (Option Int))) (histogram_2 : (List Int)) (current_2 : (List Int)) (counters_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) (counters_2))) ((0 : Int))))) (PreH2 : ((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) (counters_2))) ((0 : Int))) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current_2)) = n_pre)) (PreH20 : ((Zlength (histogram_2)) = 10)) (PreH21 : ((Zlength (counters_2)) = 10)) (PreH22 : ((Zlength (mixed_output_2)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current_2) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current_2) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit) (histogram_2) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters_2) ((0 : Int))))) ∧ ((Znth (digit) (counters_2) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current_2 exponent)) (PreH37 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH38 : (BucketPlacementProgress current_2 exponent (i + 1) histogram_2 counters_2 mixed_output_2)) ,
  (intArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth ((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2)) (0 : Int))) ((Some ((Znth i current_2 (0 : Int))))) (mixed_output_2)))
  ** (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2)))
|--
  EX mixed_output : (List (Option Int)), EX counters : (List Int), EX histogram : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= (i - 1))) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent ((i - 1) + 1) histogram counters mixed_output) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output_2 : (List (Option Int))) (histogram_2 : (List Int)) (current_2 : (List Int)) (counters_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) (counters_2))) ((0 : Int))))) (PreH2 : ((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) (counters_2))) ((0 : Int))) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current_2)) = n_pre)) (PreH20 : ((Zlength (histogram_2)) = 10)) (PreH21 : ((Zlength (counters_2)) = 10)) (PreH22 : ((Zlength (mixed_output_2)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current_2) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current_2) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit) (histogram_2) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters_2) ((0 : Int))))) ∧ ((Znth (digit) (counters_2) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current_2 exponent)) (PreH37 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH38 : (BucketPlacementProgress current_2 exponent (i + 1) histogram_2 counters_2 mixed_output_2)) ,
  TT && emp 
|--
  EX histogram : (List Int),
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2)))) = 10) ” &&
  “ ((Zlength ((replace_Znth ((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2)) (0 : Int))) ((Some ((Znth i current_2 (0 : Int))))) (mixed_output_2)))) = 1000) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (Zlength (input))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= (Zlength (input)))) ∧ ((0 : Int) <= (Znth (digit) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2))) ((0 : Int))))) ∧ ((Znth (digit) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2))) ((0 : Int))) <= (Zlength (input))))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= (i - 1))) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2))) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current_2) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2))) ((0 : Int))) <= (Zlength (input))))) ” &&
  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram) ” &&
  “ (BucketPlacementProgress current_2 exponent ((i - 1) + 1) histogram (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2)) (replace_Znth ((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10) counters_2 (0 : Int)) - 1)) (counters_2)) (0 : Int))) ((Some ((Znth i current_2 (0 : Int))))) (mixed_output_2))) ”
  &&  emp
)

noncomputable def sort_entail_wit_18 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (counters : (List Int)) (histogram_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_4) (current_2) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_4) (current_2) ((0 : Int))) exponent) 10) < 10)))) (PreH18 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit) (histogram_2) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_5) (current_2) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_5) (current_2) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value)) (PreH21 : (DecimalExponent exponent)) (PreH22 : (RadixPassState input current_2 exponent)) (PreH23 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH24 : (BucketPlacementProgress current_2 exponent (i + 1) histogram_2 counters mixed_output)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  EX pass_output : (List Int), EX bucket_starts : (List Int), EX histogram : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (bucket_starts)) = 10) ” &&
  “ ((Zlength (pass_output)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (StableDigitPass current pass_output exponent) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (counters : (List Int)) (histogram_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_4) (current_2) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_4) (current_2) ((0 : Int))) exponent) 10) < 10)))) (PreH18 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram_2) ((0 : Int)))) ∧ ((Znth (digit) (histogram_2) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_5) (current_2) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_5) (current_2) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value)) (PreH21 : (DecimalExponent exponent)) (PreH22 : (RadixPassState input current_2 exponent)) (PreH23 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH24 : (BucketPlacementProgress current_2 exponent (i + 1) histogram_2 counters mixed_output)) ,
  (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  EX pass_output : (List Int), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current_2)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (pass_output)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current_2 exponent) ” &&
  “ (DigitHistogramPrefix current_2 exponent n_pre histogram) ” &&
  “ (StableDigitPass current_2 pass_output exponent) ”
  &&  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
)

noncomputable def sort_entail_wit_19 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram : (List Int)) (bucket_starts_2 : (List Int)) (pass_output_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH14 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)))) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current_2 exponent)) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram)) (PreH19 : (StableDigitPass current_2 pass_output_2 exponent)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts_2)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  EX working : (List Int), EX pass_output : (List Int), EX bucket_starts : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 10) ” &&
  “ ((Zlength (pass_output)) = n_pre) ” &&
  “ ((Zlength (working)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working) ((0 : Int))))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working (0 : Int)) ”
  &&  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram : (List Int)) (bucket_starts_2 : (List Int)) (pass_output_2 : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH14 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((0 : Int) <= (Znth (k_4) (current_2) ((0 : Int)))) ∧ ((Znth (k_4) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)))) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current_2 exponent)) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram)) (PreH19 : (StableDigitPass current_2 pass_output_2 exponent)) ,
  TT && emp 
|--
  EX current : (List Int),
  “ ((Zlength (current)) = (Zlength (input))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (input))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (input)))) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int))))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999))) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output_2 exponent) ” &&
  “ (RadixCopyPrefix current pass_output_2 current_2 (0 : Int)) ”
  &&  emp
)

noncomputable def sort_entail_wit_20 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working_2 : (List Int)) (pass_output_2 : (List Int)) (bucket_starts_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working_2)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working_2) ((0 : Int))))) ∧ ((Znth (k_2) (working_2) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (StableDigitPass current_2 pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current_2 pass_output_2 working_2 i)) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - (0 : Int)) pass_output_2 (0 : Int))) (working_2)))
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  EX working : (List Int), EX pass_output : (List Int), EX bucket_starts : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 10) ” &&
  “ ((Zlength (pass_output)) = n_pre) ” &&
  “ ((Zlength (working)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working) ((0 : Int))))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working (i + 1)) ”
  &&  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working_2 : (List Int)) (pass_output_2 : (List Int)) (bucket_starts_2 : (List Int)) (current_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working_2)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current_2) ((0 : Int)))) ∧ ((Znth (k_2) (current_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working_2) ((0 : Int))))) ∧ ((Znth (k_2) (working_2) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (StableDigitPass current_2 pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current_2 pass_output_2 working_2 i)) ,
  TT && emp 
|--
  EX current : (List Int),
  “ ((Zlength (current)) = (Zlength (input))) ” &&
  “ ((Zlength ((replace_Znth (i) ((Znth (i - (0 : Int)) pass_output_2 (0 : Int))) (working_2)))) = (Zlength (input))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (input))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (input)))) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) ((replace_Znth (i) ((Znth (i - (0 : Int)) pass_output_2 (0 : Int))) (working_2))) ((0 : Int))))) ∧ ((Znth (k_2) ((replace_Znth (i) ((Znth (i - (0 : Int)) pass_output_2 (0 : Int))) (working_2))) ((0 : Int))) <= 999999999))) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output_2 exponent) ” &&
  “ (RadixCopyPrefix current pass_output_2 (replace_Znth (i) ((Znth (i - (0 : Int)) pass_output_2 (0 : Int))) (working_2)) (i + 1)) ”
  &&  emp
)

noncomputable def sort_entail_wit_21 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output_2 : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((((0 : Int) <= (Znth (k_4) (current) ((0 : Int)))) ∧ ((Znth (k_4) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (working) ((0 : Int))))) ∧ ((Znth (k_4) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current pass_output_2 working i)) ,
  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  EX pass_output : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (pass_output)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ (1 <= (exponent * 10)) ” &&
  “ ((exponent * 10) <= 1000000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int)))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent (exponent * 10)) ” &&
  “ (RadixPassState input pass_output (exponent * 10)) ”
  &&  (intArray.full a_pre n_pre pass_output)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output_2 : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((((0 : Int) <= (Znth (k_4) (current) ((0 : Int)))) ∧ ((Znth (k_4) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (working) ((0 : Int))))) ∧ ((Znth (k_4) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current pass_output_2 working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (RadixPassState input working (exponent * 10)) ” &&
  “ (DecimalExponent (exponent * 10)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (working) ((0 : Int)))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ”
  &&  (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
)

noncomputable def sort_entail_wit_21_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output_2 : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((((0 : Int) <= (Znth (k_4) (current) ((0 : Int)))) ∧ ((Znth (k_4) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (working) ((0 : Int))))) ∧ ((Znth (k_4) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current pass_output_2 working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (RadixPassState input working (exponent * 10)) ”

noncomputable def sort_entail_wit_21_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output_2 : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((((0 : Int) <= (Znth (k_4) (current) ((0 : Int)))) ∧ ((Znth (k_4) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (working) ((0 : Int))))) ∧ ((Znth (k_4) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current pass_output_2 working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (DecimalExponent (exponent * 10)) ”

noncomputable def sort_entail_wit_21_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output_2 : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((((0 : Int) <= (Znth (k_4) (current) ((0 : Int)))) ∧ ((Znth (k_4) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (working) ((0 : Int))))) ∧ ((Znth (k_4) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current pass_output_2 working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (working) ((0 : Int)))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999))) ”

noncomputable def sort_entail_wit_21_split_goal_4 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output_2 : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((((0 : Int) <= (Znth (k_4) (current) ((0 : Int)))) ∧ ((Znth (k_4) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (working) ((0 : Int))))) ∧ ((Znth (k_4) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current pass_output_2 working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ”

noncomputable def sort_entail_wit_21_split_goal_spatial : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output_2 : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((((((0 : Int) <= (Znth (k_4) (current) ((0 : Int)))) ∧ ((Znth (k_4) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (pass_output_2) ((0 : Int))))) ∧ ((Znth (k_4) (pass_output_2) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_4) (working) ((0 : Int))))) ∧ ((Znth (k_4) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output_2 exponent)) (PreH22 : (RadixCopyPrefix current pass_output_2 working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)

noncomputable def sort_entail_wit_22 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (pass_output : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10))) (PreH10 : ((exponent * 10) <= 1000000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (pass_output) ((0 : Int)))) ∧ ((Znth (k_4) (pass_output) ((0 : Int))) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent (exponent * 10))) (PreH16 : (RadixPassState input pass_output (exponent * 10))) ,
  (intArray.full a_pre n_pre pass_output)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= (exponent * 10)) ” &&
  “ ((exponent * 10) <= 1000000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent (exponent * 10)) ” &&
  “ (RadixPassState input current (exponent * 10)) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
) \/
(
forall (n_pre : Int) (input : (List Int)) (pass_output : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10))) (PreH10 : ((exponent * 10) <= 1000000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (pass_output) ((0 : Int)))) ∧ ((Znth (k_4) (pass_output) ((0 : Int))) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent (exponent * 10))) (PreH16 : (RadixPassState input pass_output (exponent * 10))) ,
  TT && emp 
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int)))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ”
  &&  emp
)

noncomputable def sort_entail_wit_22_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (pass_output : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10))) (PreH10 : ((exponent * 10) <= 1000000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (pass_output) ((0 : Int)))) ∧ ((Znth (k_4) (pass_output) ((0 : Int))) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent (exponent * 10))) (PreH16 : (RadixPassState input pass_output (exponent * 10))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int)))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_22_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (pass_output : (List Int)) (max_value : Int) (exponent : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10))) (PreH10 : ((exponent * 10) <= 1000000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (input) ((0 : Int)))) ∧ ((Znth (k_3) (input) ((0 : Int))) <= 999999999)))) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> (((0 : Int) <= (Znth (k_4) (pass_output) ((0 : Int)))) ∧ ((Znth (k_4) (pass_output) ((0 : Int))) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent (exponent * 10))) (PreH16 : (RadixPassState input pass_output (exponent * 10))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_entail_wit_23 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (input) ((0 : Int)))) ∧ ((Znth (k_2) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (current) ((0 : Int)))) ∧ ((Znth (k_3) (current) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current exponent)) ,
  ((( &( "max_value" ) )) # Int |-> (max_value))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  EX final : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (final)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ (Permutation input final) ” &&
  “ (increasing final) ”
  &&  (intArray.full a_pre n_pre final)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
  ** ((( &( "max_value" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (input) ((0 : Int)))) ∧ ((Znth (k_2) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (current) ((0 : Int)))) ∧ ((Znth (k_3) (current) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current exponent)) ,
  TT && emp 
|--
  “ (increasing current) ” &&
  “ (Permutation input current) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ”
  &&  emp
)

noncomputable def sort_entail_wit_23_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (input) ((0 : Int)))) ∧ ((Znth (k_2) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (current) ((0 : Int)))) ∧ ((Znth (k_3) (current) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current exponent)) ,
  (increasing current)

noncomputable def sort_entail_wit_23_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (input) ((0 : Int)))) ∧ ((Znth (k_2) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (current) ((0 : Int)))) ∧ ((Znth (k_3) (current) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current exponent)) ,
  (Permutation input current)

noncomputable def sort_entail_wit_23_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (input) ((0 : Int)))) ∧ ((Znth (k_2) (input) ((0 : Int))) <= 999999999)))) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> (((0 : Int) <= (Znth (k_3) (current) ((0 : Int)))) ∧ ((Znth (k_3) (current) ((0 : Int))) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value)) (PreH13 : (DecimalExponent exponent)) (PreH14 : (RadixPassState input current exponent)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))

noncomputable def sort_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  (intArray.full a_pre n_pre input)
|--
  EX output : (List Int),
  “ ((Zlength (output)) = n_pre) ” &&
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full a_pre n_pre output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  TT && emp 
|--
  “ (increasing input) ” &&
  “ (Permutation input input) ”
  &&  emp
)

noncomputable def sort_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  (increasing input)

noncomputable def sort_return_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  (Permutation input input)

noncomputable def sort_return_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (final : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (final)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH6 : (Permutation input final)) (PreH7 : (increasing final)) ,
  (intArray.full a_pre n_pre final)
|--
  EX output : (List Int),
  “ ((Zlength (output)) = n_pre) ” &&
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full a_pre n_pre output)

noncomputable def sort_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999)))) ,
  (intArray.full a_pre n_pre input)
|--
  “ (n_pre > 1) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ∧ ((Znth (i) (input) ((0 : Int))) <= 999999999))) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre input)

noncomputable def sort_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input i max_value) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)

noncomputable def sort_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ ((Znth i input (0 : Int)) > max_value) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input i max_value) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)

noncomputable def sort_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (exponent : Int) (max_value : Int) (digit : Int) (zero_prefix : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) ((0 : Int))) = (0 : Int)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (zero_prefix)) = digit) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= digit) ” &&
  “ (digit <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) ((0 : Int))) = (0 : Int))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : ((0 : Int) < (Z.quot max_value exponent))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH16 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent i counts) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i current (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ” &&
  “ (i <= INT_MAX) ” &&
  “ (exponent <= INT_MAX) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (exponent >= INT_MIN) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent i counts) ”
  &&  (((( &( "count" ) ) + ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) * sizeof(INT)))) # Int |-> ((Znth (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) counts (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) (0 : Int) 10 counts)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (counts : (List Int)) (current : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value)) (PreH28 : (DecimalExponent exponent)) (PreH29 : (RadixPassState input current exponent)) (PreH30 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ” &&
  “ (i <= INT_MAX) ” &&
  “ (exponent <= INT_MAX) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (exponent >= INT_MIN) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (counts)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((0 : Int) <= (Znth (digit) (counts) ((0 : Int)))) ∧ ((Znth (digit) (counts) ((0 : Int))) <= i))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent i counts) ”
  &&  (((( &( "count" ) ) + ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) (0 : Int) 10 counts)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (totals)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= digit) ” &&
  “ (digit <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals digit) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |-> ((Znth digit totals (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (totals)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= digit) ” &&
  “ (digit <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals digit) ”
  &&  (((( &( "count" ) ) + ((digit - 1) * sizeof(INT)))) # Int |-> ((Znth (digit - 1) totals (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (digit - 1) (0 : Int) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (totals : (List Int)) (histogram : (List Int)) (current : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : ((0 : Int) <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : ((0 : Int) < (Z.quot max_value exponent))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre)))) (PreH18 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value)) (PreH20 : (DecimalExponent exponent)) (PreH21 : (RadixPassState input current exponent)) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH23 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (totals)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= digit) ” &&
  “ (digit <= 10) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < 10)) -> (((0 : Int) <= (Znth (k_3) (histogram) ((0 : Int)))) ∧ ((Znth (k_3) (histogram) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < 10)) -> (((0 : Int) <= (Znth (k_4) (totals) ((0 : Int)))) ∧ ((Znth (k_4) (totals) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals digit) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH18 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH19 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value)) (PreH21 : (DecimalExponent exponent)) (PreH22 : (RadixPassState input current exponent)) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH24 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i current (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)

noncomputable def sort_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH3 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH4 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH5 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH6 : (max_value <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (input)) = n_pre)) (PreH14 : ((Zlength (current)) = n_pre)) (PreH15 : ((Zlength (histogram)) = 10)) (PreH16 : ((Zlength (counters)) = 10)) (PreH17 : ((Zlength (mixed_output)) = 1000)) (PreH18 : ((0 : Int) <= max_value)) (PreH19 : (max_value <= 999999999)) (PreH20 : (1 <= exponent)) (PreH21 : (exponent <= 100000000)) (PreH22 : ((0 : Int) < (Z.quot max_value exponent))) (PreH23 : ((-1) <= i)) (PreH24 : (i < n_pre)) (PreH25 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH27 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH28 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH29 : (PrefixMaximum input n_pre max_value)) (PreH30 : (DecimalExponent exponent)) (PreH31 : (RadixPassState input current exponent)) (PreH32 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH33 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  (((( &( "count" ) ) + ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) * sizeof(INT)))) # Int |-> ((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) (0 : Int) 10 counters)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)

noncomputable def sort_partial_solve_wit_13 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH2 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH3 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH4 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (max_value >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : ((Zlength (input)) = n_pre)) (PreH13 : ((Zlength (current)) = n_pre)) (PreH14 : ((Zlength (histogram)) = 10)) (PreH15 : ((Zlength (counters)) = 10)) (PreH16 : ((Zlength (mixed_output)) = 1000)) (PreH17 : ((0 : Int) <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : ((0 : Int) < (Z.quot max_value exponent))) (PreH22 : ((-1) <= i)) (PreH23 : (i < n_pre)) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH26 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH27 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH28 : (PrefixMaximum input n_pre max_value)) (PreH29 : (DecimalExponent exponent)) (PreH30 : (RadixPassState input current exponent)) (PreH31 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH32 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  (((( &( "count" ) ) + ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) (0 : Int) 10 counters)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)

noncomputable def sort_partial_solve_wit_14 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))))) (PreH2 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current exponent)) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH38 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000) ” &&
  “ (exponent <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (exponent >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  (((( &( "count" ) ) + ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) * sizeof(INT)))) # Int |-> ((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)) (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) (0 : Int) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)

noncomputable def sort_partial_solve_wit_15 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))))) (PreH2 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current exponent)) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH38 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000) ” &&
  “ (exponent <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (exponent >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i current (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)

noncomputable def sort_partial_solve_wit_16 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (mixed_output : (List (Option Int))) (histogram : (List Int)) (current : (List Int)) (counters : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))))) (PreH2 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH8 : ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10)) (PreH9 : (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))))) (PreH10 : ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= (0 : Int))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : ((0 : Int) <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : ((0 : Int) < (Z.quot max_value exponent))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH31 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10)))) (PreH32 : forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre)))) (PreH33 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value)) (PreH35 : (DecimalExponent exponent)) (PreH36 : (RadixPassState input current exponent)) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH38 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ((replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) - 1)) (counters))) ((0 : Int))) < 1000) ” &&
  “ (exponent <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (exponent >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ” &&
  “ (max_value <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (max_value >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((Zlength (counters)) = 10) ” &&
  “ ((Zlength (mixed_output)) = 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10))) ∧ ((Z.rem (Z.quot (Znth (k_2) (current) ((0 : Int))) exponent) 10) < 10))) ” &&
  “ forall (digit : Int) , ((((0 : Int) <= digit) ∧ (digit < 10)) -> (((((0 : Int) <= (Znth (digit) (histogram) ((0 : Int)))) ∧ ((Znth (digit) (histogram) ((0 : Int))) <= n_pre)) ∧ ((0 : Int) <= (Znth (digit) (counters) ((0 : Int))))) ∧ ((Znth (digit) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= i)) -> ((1 <= (Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int)))) ∧ ((Znth ((Z.rem (Z.quot (Znth (k_3) (current) ((0 : Int))) exponent) 10)) (counters) ((0 : Int))) <= n_pre))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  (((( &( "output" ) ) + ((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)) (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i ( &( "output" ) ) (Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)) (0 : Int)) (0 : Int) 1000 mixed_output)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth ((Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) (((Znth (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10) counters (0 : Int)) - 1)) (counters)))

noncomputable def sort_partial_solve_wit_17 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working) ((0 : Int))))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output exponent)) (PreH22 : (RadixCopyPrefix current pass_output working i)) ,
  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 10) ” &&
  “ ((Zlength (pass_output)) = n_pre) ” &&
  “ ((Zlength (working)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working) ((0 : Int))))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working i) ”
  &&  (((( &( "output" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth (i - (0 : Int)) pass_output (0 : Int))))
  ** (intArray.missing_i ( &( "output" ) ) i (0 : Int) n_pre pass_output)
  ** (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)

noncomputable def sort_partial_solve_wit_18 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (working : (List Int)) (pass_output : (List Int)) (bucket_starts : (List Int)) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : ((0 : Int) <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : ((0 : Int) < (Z.quot max_value exponent))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999)))) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working) ((0 : Int))))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (StableDigitPass current pass_output exponent)) (PreH22 : (RadixCopyPrefix current pass_output working i)) ,
  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 10) ” &&
  “ ((Zlength (pass_output)) = n_pre) ” &&
  “ ((Zlength (working)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth (k) (input) ((0 : Int)))) ∧ ((Znth (k) (input) ((0 : Int))) <= 999999999))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((((((0 : Int) <= (Znth (k_2) (current) ((0 : Int)))) ∧ ((Znth (k_2) (current) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (pass_output) ((0 : Int))))) ∧ ((Znth (k_2) (pass_output) ((0 : Int))) <= 999999999)) ∧ ((0 : Int) <= (Znth (k_2) (working) ((0 : Int))))) ∧ ((Znth (k_2) (working) ((0 : Int))) <= 999999999))) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working i) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre i (0 : Int) n_pre working)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)


structure VC_Correct : Type where
  proof_of_sort_safety_wit_1 : sort_safety_wit_1
  proof_of_sort_safety_wit_2 : sort_safety_wit_2
  proof_of_sort_safety_wit_3 : sort_safety_wit_3
  proof_of_sort_safety_wit_4 : sort_safety_wit_4
  proof_of_sort_safety_wit_5 : sort_safety_wit_5
  proof_of_sort_safety_wit_6 : sort_safety_wit_6
  proof_of_sort_safety_wit_7 : sort_safety_wit_7
  proof_of_sort_safety_wit_8 : sort_safety_wit_8
  proof_of_sort_safety_wit_9 : sort_safety_wit_9
  proof_of_sort_safety_wit_10 : sort_safety_wit_10
  proof_of_sort_safety_wit_11 : sort_safety_wit_11
  proof_of_sort_safety_wit_12 : sort_safety_wit_12
  proof_of_sort_safety_wit_13 : sort_safety_wit_13
  proof_of_sort_safety_wit_14 : sort_safety_wit_14
  proof_of_sort_safety_wit_15 : sort_safety_wit_15
  proof_of_sort_safety_wit_16 : sort_safety_wit_16
  proof_of_sort_safety_wit_18 : sort_safety_wit_18
  proof_of_sort_safety_wit_19 : sort_safety_wit_19
  proof_of_sort_safety_wit_20 : sort_safety_wit_20
  proof_of_sort_safety_wit_22 : sort_safety_wit_22
  proof_of_sort_safety_wit_23 : sort_safety_wit_23
  proof_of_sort_safety_wit_24 : sort_safety_wit_24
  proof_of_sort_safety_wit_25 : sort_safety_wit_25
  proof_of_sort_safety_wit_26 : sort_safety_wit_26
  proof_of_sort_safety_wit_27 : sort_safety_wit_27
  proof_of_sort_safety_wit_28 : sort_safety_wit_28
  proof_of_sort_safety_wit_29 : sort_safety_wit_29
  proof_of_sort_safety_wit_30 : sort_safety_wit_30
  proof_of_sort_safety_wit_31 : sort_safety_wit_31
  proof_of_sort_safety_wit_32 : sort_safety_wit_32
  proof_of_sort_safety_wit_33 : sort_safety_wit_33
  proof_of_sort_safety_wit_34 : sort_safety_wit_34
  proof_of_sort_safety_wit_35 : sort_safety_wit_35
  proof_of_sort_safety_wit_36 : sort_safety_wit_36
  proof_of_sort_return_wit_2 : sort_return_wit_2
  proof_of_sort_partial_solve_wit_1 : sort_partial_solve_wit_1
  proof_of_sort_partial_solve_wit_2 : sort_partial_solve_wit_2
  proof_of_sort_partial_solve_wit_3 : sort_partial_solve_wit_3
  proof_of_sort_partial_solve_wit_4 : sort_partial_solve_wit_4
  proof_of_sort_partial_solve_wit_5 : sort_partial_solve_wit_5
  proof_of_sort_partial_solve_wit_6 : sort_partial_solve_wit_6
  proof_of_sort_partial_solve_wit_7 : sort_partial_solve_wit_7
  proof_of_sort_partial_solve_wit_8 : sort_partial_solve_wit_8
  proof_of_sort_partial_solve_wit_9 : sort_partial_solve_wit_9
  proof_of_sort_partial_solve_wit_10 : sort_partial_solve_wit_10
  proof_of_sort_partial_solve_wit_11 : sort_partial_solve_wit_11
  proof_of_sort_partial_solve_wit_12 : sort_partial_solve_wit_12
  proof_of_sort_partial_solve_wit_13 : sort_partial_solve_wit_13
  proof_of_sort_partial_solve_wit_14 : sort_partial_solve_wit_14
  proof_of_sort_partial_solve_wit_15 : sort_partial_solve_wit_15
  proof_of_sort_partial_solve_wit_16 : sort_partial_solve_wit_16
  proof_of_sort_partial_solve_wit_17 : sort_partial_solve_wit_17
  proof_of_sort_partial_solve_wit_18 : sort_partial_solve_wit_18
  proof_of_sort_safety_wit_17 : sort_safety_wit_17
  proof_of_sort_safety_wit_21 : sort_safety_wit_21
  proof_of_sort_entail_wit_1 : sort_entail_wit_1
  proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1
  proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2
  proof_of_sort_entail_wit_3 : sort_entail_wit_3
  proof_of_sort_entail_wit_4 : sort_entail_wit_4
  proof_of_sort_entail_wit_5 : sort_entail_wit_5
  proof_of_sort_entail_wit_6 : sort_entail_wit_6
  proof_of_sort_entail_wit_7 : sort_entail_wit_7
  proof_of_sort_entail_wit_8 : sort_entail_wit_8
  proof_of_sort_entail_wit_9 : sort_entail_wit_9
  proof_of_sort_entail_wit_10 : sort_entail_wit_10
  proof_of_sort_entail_wit_11 : sort_entail_wit_11
  proof_of_sort_entail_wit_12 : sort_entail_wit_12
  proof_of_sort_entail_wit_13 : sort_entail_wit_13
  proof_of_sort_entail_wit_14 : sort_entail_wit_14
  proof_of_sort_entail_wit_15 : sort_entail_wit_15
  proof_of_sort_entail_wit_16 : sort_entail_wit_16
  proof_of_sort_entail_wit_17 : sort_entail_wit_17
  proof_of_sort_entail_wit_18 : sort_entail_wit_18
  proof_of_sort_entail_wit_19 : sort_entail_wit_19
  proof_of_sort_entail_wit_20 : sort_entail_wit_20
  proof_of_sort_entail_wit_21 : sort_entail_wit_21
  proof_of_sort_entail_wit_22 : sort_entail_wit_22
  proof_of_sort_entail_wit_23 : sort_entail_wit_23
  proof_of_sort_return_wit_1 : sort_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_goal
