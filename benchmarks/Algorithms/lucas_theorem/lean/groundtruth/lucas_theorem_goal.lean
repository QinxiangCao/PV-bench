import SimpleC.SL.SeparationLogic

import Algorithms.lucas_theorem.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.lucas_theorem.lean.groundtruth.lucas_theorem_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance lucas_theorem_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def binomial_digit_mod_prime_safety_wit_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > upper_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ False ”

noncomputable def binomial_digit_mod_prime_safety_wit_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= upper_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ ((upper_pre - lower_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (upper_pre - lower_pre)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_3 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ ((upper_pre - lower_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (upper_pre - lower_pre)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_4 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "numerator" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> ((upper_pre - lower_pre)))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_5 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "numerator" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_6 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "denominator" ) )) # Int |->_)
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> ((upper_pre - lower_pre)))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_7 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "denominator" ) )) # Int |->_)
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_8 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "denominator" ) )) # Int |-> (1))
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> ((upper_pre - lower_pre)))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_9 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "denominator" ) )) # Int |-> (1))
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_10 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "factor" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((upper_pre - lower_pre) + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((upper_pre - lower_pre) + i)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_11 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "factor" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((upper_pre - lower_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (upper_pre - lower_pre)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_12 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "factor" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((upper_pre - lower) + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((upper_pre - lower) + i)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_13 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "factor" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((upper_pre - lower) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (upper_pre - lower)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_14 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * ((upper_pre - lower_pre) + i)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower_pre) + i))) ”
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * ((upper_pre - lower_pre) + i)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower_pre) + i))) ”
)

noncomputable def binomial_digit_mod_prime_safety_wit_14_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * ((upper_pre - lower_pre) + i)) <= INT_MAX) ”

noncomputable def binomial_digit_mod_prime_safety_wit_14_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower_pre) + i))) ”

noncomputable def binomial_digit_mod_prime_safety_wit_15 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * ((upper_pre - lower) + i)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower) + i))) ”
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * ((upper_pre - lower) + i)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower) + i))) ”
)

noncomputable def binomial_digit_mod_prime_safety_wit_15_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * ((upper_pre - lower) + i)) <= INT_MAX) ”

noncomputable def binomial_digit_mod_prime_safety_wit_15_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower) + i))) ”

noncomputable def binomial_digit_mod_prime_safety_wit_16 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower_pre) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((denominator * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (denominator * i)) ”
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower_pre) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((denominator * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (denominator * i)) ”
)

noncomputable def binomial_digit_mod_prime_safety_wit_16_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower_pre) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((denominator * i) <= INT_MAX) ”

noncomputable def binomial_digit_mod_prime_safety_wit_16_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower_pre) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((INT_MIN) <= (denominator * i)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_17 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((denominator * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (denominator * i)) ”
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((denominator * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (denominator * i)) ”
)

noncomputable def binomial_digit_mod_prime_safety_wit_17_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((denominator * i) <= INT_MAX) ”

noncomputable def binomial_digit_mod_prime_safety_wit_17_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |->_)
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((INT_MIN) <= (denominator * i)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_18 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |-> ((denominator * i)))
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower_pre) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((numerator * ((upper_pre - lower_pre) + i)) ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_19 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |-> ((denominator * i)))
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((numerator * ((upper_pre - lower) + i)) ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_20 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |-> ((denominator * i)))
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower_pre) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower_pre) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> ((Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre)))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((denominator * i) ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_21 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int |-> ((denominator * i)))
  ** ((( &( "numerator_product" ) )) # Int |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((denominator * i) ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_22 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> ((Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre)))
  ** ((( &( "denominator" ) )) # Int |-> ((Z.rem (denominator * i) prime_pre)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_23 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)))
  ** ((( &( "denominator" ) )) # Int |-> ((Z.rem (denominator * i) prime_pre)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_24 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre))) (PreH8 : (lower_pre > (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : ((0 : Int) <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : ((0 : Int) <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : ((0 : Int) <= (prime_pre - 2))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((prime_pre - 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (prime_pre - 2)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_25 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre))) (PreH8 : (lower_pre > (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : ((0 : Int) <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : ((0 : Int) <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : ((0 : Int) <= (prime_pre - 2))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def binomial_digit_mod_prime_safety_wit_26 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre))) (PreH8 : ((0 : Int) <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : ((0 : Int) <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : ((0 : Int) <= (prime_pre - 2))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((prime_pre - 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (prime_pre - 2)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_27 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre))) (PreH8 : ((0 : Int) <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : ((0 : Int) <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : ((0 : Int) <= (prime_pre - 2))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def binomial_digit_mod_prime_safety_wit_28 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * retval)) ”
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * retval)) ”
)

noncomputable def binomial_digit_mod_prime_safety_wit_28_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * retval) <= INT_MAX) ”

noncomputable def binomial_digit_mod_prime_safety_wit_28_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((INT_MIN) <= (numerator * retval)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_29 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * retval)) ”
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numerator * retval)) ”
)

noncomputable def binomial_digit_mod_prime_safety_wit_29_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * retval) <= INT_MAX) ”

noncomputable def binomial_digit_mod_prime_safety_wit_29_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((INT_MIN) <= (numerator * retval)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_30 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |-> ((numerator * retval)))
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((numerator * retval) ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_31 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "answer" ) )) # Int |-> ((numerator * retval)))
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((numerator * retval) ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_entail_wit_1_1 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  ((( &( "lower" ) )) # Int |-> ((upper_pre - lower_pre)))
|--
  EX lower : Int,
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower = (upper_pre - lower_pre)) ” &&
  “ (lower_pre > (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= (upper_pre - lower)) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (lower + 1)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower prime_pre 1 1 1) ”
  &&  ((( &( "lower" ) )) # Int |-> (lower))
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre 1 1 1) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre 1 1 1)

noncomputable def binomial_digit_mod_prime_entail_wit_1_2 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (lower_pre + 1)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) ,
  (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1)

noncomputable def binomial_digit_mod_prime_entail_wit_2_1 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (lower_pre + 1)) ” &&
  “ ((0 : Int) <= (Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre)) ” &&
  “ ((Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (denominator * i) prime_pre)) ” &&
  “ ((Z.rem (denominator * i) prime_pre) < prime_pre) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower_pre prime_pre (i + 1) (Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre) (Z.rem (denominator * i) prime_pre)) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre (i + 1) (Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre) (Z.rem (denominator * i) prime_pre)) ” &&
  “ ((Z.rem (denominator * i) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (denominator * i) prime_pre)) ” &&
  “ ((Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre)) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_2_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  (DigitProductProgress upper_pre lower_pre prime_pre (i + 1) (Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre) (Z.rem (denominator * i) prime_pre))

noncomputable def binomial_digit_mod_prime_entail_wit_2_1_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((Z.rem (denominator * i) prime_pre) < prime_pre)

noncomputable def binomial_digit_mod_prime_entail_wit_2_1_split_goal_3 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((0 : Int) <= (Z.rem (denominator * i) prime_pre))

noncomputable def binomial_digit_mod_prime_entail_wit_2_1_split_goal_4 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre) < prime_pre)

noncomputable def binomial_digit_mod_prime_entail_wit_2_1_split_goal_5 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  ((0 : Int) <= (Z.rem (numerator * ((upper_pre - lower_pre) + i)) prime_pre))

noncomputable def binomial_digit_mod_prime_entail_wit_2_2 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "lower" ) )) # Int |-> (lower))
|--
  EX lower_2 : Int,
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower_2 = (upper_pre - lower_pre)) ” &&
  “ (lower_pre > (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower_2) ” &&
  “ (lower_2 <= (upper_pre - lower_2)) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (lower_2 + 1)) ” &&
  “ ((0 : Int) <= (Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) ” &&
  “ ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (denominator * i) prime_pre)) ” &&
  “ ((Z.rem (denominator * i) prime_pre) < prime_pre) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower_2 prime_pre (i + 1) (Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre) (Z.rem (denominator * i) prime_pre)) ”
  &&  ((( &( "lower" ) )) # Int |-> (lower_2))
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre (i + 1) (Z.rem (numerator * ((upper_pre - (upper_pre - lower_pre)) + i)) prime_pre) (Z.rem (denominator * i) prime_pre)) ” &&
  “ ((Z.rem (denominator * i) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (denominator * i) prime_pre)) ” &&
  “ ((Z.rem (numerator * ((upper_pre - (upper_pre - lower_pre)) + i)) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (numerator * ((upper_pre - (upper_pre - lower_pre)) + i)) prime_pre)) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_2_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre (i + 1) (Z.rem (numerator * ((upper_pre - (upper_pre - lower_pre)) + i)) prime_pre) (Z.rem (denominator * i) prime_pre))

noncomputable def binomial_digit_mod_prime_entail_wit_2_2_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((Z.rem (denominator * i) prime_pre) < prime_pre)

noncomputable def binomial_digit_mod_prime_entail_wit_2_2_split_goal_3 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((0 : Int) <= (Z.rem (denominator * i) prime_pre))

noncomputable def binomial_digit_mod_prime_entail_wit_2_2_split_goal_4 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((Z.rem (numerator * ((upper_pre - (upper_pre - lower_pre)) + i)) prime_pre) < prime_pre)

noncomputable def binomial_digit_mod_prime_entail_wit_2_2_split_goal_5 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((0 : Int) <= (Z.rem (numerator * ((upper_pre - (upper_pre - lower_pre)) + i)) prime_pre))

noncomputable def binomial_digit_mod_prime_entail_wit_3_1 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i > lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= numerator) ” &&
  “ (numerator < prime_pre) ” &&
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i > lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_3_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (PreH1 : (i > lower_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator)) ,
  (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)

noncomputable def binomial_digit_mod_prime_entail_wit_3_2 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower_2 : Int) (PreH1 : (i > lower_2)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_2 = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower_2)) (PreH11 : (lower_2 <= (upper_pre - lower_2))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower_2 + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_2 prime_pre i numerator denominator)) ,
  ((( &( "lower" ) )) # Int |-> (lower_2))
|--
  EX lower : Int,
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower = (upper_pre - lower_pre)) ” &&
  “ (lower_pre > (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= (upper_pre - lower)) ” &&
  “ ((0 : Int) <= numerator) ” &&
  “ (numerator < prime_pre) ” &&
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator) ”
  &&  ((( &( "lower" ) )) # Int |-> (lower))
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower_2 : Int) (PreH1 : (i > lower_2)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_2 = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower_2)) (PreH11 : (lower_2 <= (upper_pre - lower_2))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower_2 + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_2 prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre ((upper_pre - lower_pre) + 1) numerator denominator) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_3_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower_2 : Int) (PreH1 : (i > lower_2)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_2 = (upper_pre - lower_pre))) (PreH9 : (lower_pre > (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= lower_2)) (PreH11 : (lower_2 <= (upper_pre - lower_2))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower_2 + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_2 prime_pre i numerator denominator)) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre ((upper_pre - lower_pre) + 1) numerator denominator)

noncomputable def binomial_digit_mod_prime_return_wit_1 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  TT && emp 
|--
  “ ((0 : Int) <= (Z.rem (numerator * retval) prime_pre)) ” &&
  “ ((Z.rem (numerator * retval) prime_pre) < prime_pre) ” &&
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (Z.rem (numerator * retval) prime_pre)) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (Z.rem (numerator * retval) prime_pre)) ” &&
  “ ((Z.rem (numerator * retval) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (numerator * retval) prime_pre)) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_return_wit_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  (BinomialDigitResidue upper_pre lower_pre prime_pre (Z.rem (numerator * retval) prime_pre))

noncomputable def binomial_digit_mod_prime_return_wit_1_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((Z.rem (numerator * retval) prime_pre) < prime_pre)

noncomputable def binomial_digit_mod_prime_return_wit_1_split_goal_3 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre))) (PreH11 : (lower_pre > (upper_pre - lower_pre))) (PreH12 : ((0 : Int) <= lower)) (PreH13 : (lower <= (upper_pre - lower))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : ((0 : Int) <= (prime_pre - 2))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((0 : Int) <= (Z.rem (numerator * retval) prime_pre))

noncomputable def binomial_digit_mod_prime_return_wit_2 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  TT && emp 
|--
  “ ((0 : Int) <= (Z.rem (numerator * retval) prime_pre)) ” &&
  “ ((Z.rem (numerator * retval) prime_pre) < prime_pre) ” &&
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (Z.rem (numerator * retval) prime_pre)) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (Z.rem (numerator * retval) prime_pre)) ” &&
  “ ((Z.rem (numerator * retval) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (numerator * retval) prime_pre)) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_return_wit_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  (BinomialDigitResidue upper_pre lower_pre prime_pre (Z.rem (numerator * retval) prime_pre))

noncomputable def binomial_digit_mod_prime_return_wit_2_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((Z.rem (numerator * retval) prime_pre) < prime_pre)

noncomputable def binomial_digit_mod_prime_return_wit_2_split_goal_3 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH4 : (PrimeForLucas prime_pre)) (PreH5 : ((0 : Int) <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre))) (PreH11 : ((0 : Int) <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : ((0 : Int) <= (prime_pre - 2))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((0 : Int) <= (Z.rem (numerator * retval) prime_pre))

noncomputable def binomial_digit_mod_prime_partial_solve_wit_1_pure : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre))) (PreH8 : (lower_pre > (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : ((0 : Int) <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : ((0 : Int) <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : ((0 : Int) <= (prime_pre - 2))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (2 <= prime_pre) ”

noncomputable def binomial_digit_mod_prime_partial_solve_wit_1_aux : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (lower : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre))) (PreH8 : (lower_pre > (upper_pre - lower_pre))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : ((0 : Int) <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : ((0 : Int) <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : ((0 : Int) <= (prime_pre - 2))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator)) ,
  TT && emp 
|--
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (2 <= prime_pre) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower = (upper_pre - lower_pre)) ” &&
  “ (lower_pre > (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= (upper_pre - lower)) ” &&
  “ ((0 : Int) <= numerator) ” &&
  “ (numerator < prime_pre) ” &&
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower prime_pre (lower + 1) numerator denominator) ”
  &&  emp

noncomputable def binomial_digit_mod_prime_partial_solve_wit_1 : Prop := binomial_digit_mod_prime_partial_solve_wit_1_pure -> binomial_digit_mod_prime_partial_solve_wit_1_aux

noncomputable def binomial_digit_mod_prime_partial_solve_wit_2_pure : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre))) (PreH8 : ((0 : Int) <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : ((0 : Int) <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : ((0 : Int) <= (prime_pre - 2))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (2 <= prime_pre) ”

noncomputable def binomial_digit_mod_prime_partial_solve_wit_2_aux : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (numerator : Int) (denominator : Int) (PreH1 : (PrimeForLucas prime_pre)) (PreH2 : ((0 : Int) <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre))) (PreH8 : ((0 : Int) <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre))) (PreH10 : ((0 : Int) <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : ((0 : Int) <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : ((0 : Int) <= (prime_pre - 2))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre)) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator)) ,
  TT && emp 
|--
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (2 <= prime_pre) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ ((0 : Int) <= numerator) ” &&
  “ (numerator < prime_pre) ” &&
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1) numerator denominator) ”
  &&  emp

noncomputable def binomial_digit_mod_prime_partial_solve_wit_2 : Prop := binomial_digit_mod_prime_partial_solve_wit_2_pure -> binomial_digit_mod_prime_partial_solve_wit_2_aux

noncomputable def lucas_theorem_safety_wit_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) ,
  ((( &( "upper" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ ((n_pre + m_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + m_pre)) ”

noncomputable def lucas_theorem_safety_wit_2 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "lower" ) )) # Int |-> (n_pre))
  ** ((( &( "upper" ) )) # Int |-> ((n_pre + m_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lucas_theorem_safety_wit_3 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (upper <= (n_pre + m_pre))) (PreH12 : ((n_pre + m_pre) <= 200000)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < prime_pre)) (PreH15 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_4 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (upper <= (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre))) (PreH13 : ((n_pre + m_pre) <= 200000)) (PreH14 : ((0 : Int) <= result)) (PreH15 : (result < prime_pre)) (PreH16 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_5 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower > (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ False ”

noncomputable def lucas_theorem_safety_wit_6 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (upper > (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre))) (PreH13 : ((n_pre + m_pre) <= 200000)) (PreH14 : ((0 : Int) <= result)) (PreH15 : (result < prime_pre)) (PreH16 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "upper_digit" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((upper ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_7 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (upper > (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre))) (PreH13 : ((n_pre + m_pre) <= 200000)) (PreH14 : ((0 : Int) <= result)) (PreH15 : (result < prime_pre)) (PreH16 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "lower_digit" ) )) # Int |->_)
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((lower ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_8 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_9 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int |->_)
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result * retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result * retval)) ”
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int |->_)
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result * retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result * retval)) ”
)

noncomputable def lucas_theorem_safety_wit_9_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int |->_)
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result * retval) <= INT_MAX) ”

noncomputable def lucas_theorem_safety_wit_9_split_goal_2 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int |->_)
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((INT_MIN) <= (result * retval)) ”

noncomputable def lucas_theorem_safety_wit_10 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int |-> ((result * retval)))
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((result * retval) ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_11 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int |-> ((result * retval)))
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * retval) prime_pre)))
|--
  “ ((upper ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_12 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int |-> ((result * retval)))
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> ((Z.quot upper prime_pre)))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * retval) prime_pre)))
|--
  “ ((lower ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_entail_wit_1 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100000) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ (LucasMachineSafe n_pre m_pre prime_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= (n_pre + m_pre)) ” &&
  “ ((n_pre + m_pre) <= (n_pre + m_pre)) ” &&
  “ ((n_pre + m_pre) <= 200000) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (n_pre + m_pre) n_pre 1) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (n_pre + m_pre) n_pre 1) ”
  &&  emp
)

noncomputable def lucas_theorem_entail_wit_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) ,
  (LucasProgress (n_pre + m_pre) n_pre prime_pre (n_pre + m_pre) n_pre 1)

noncomputable def lucas_theorem_entail_wit_2 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100000) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ (LucasMachineSafe n_pre m_pre prime_pre) ” &&
  “ ((0 : Int) < upper) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= upper) ” &&
  “ (upper <= (n_pre + m_pre)) ” &&
  “ ((n_pre + m_pre) <= 200000) ” &&
  “ ((Z.rem upper prime_pre) = (Z.rem upper prime_pre)) ” &&
  “ ((Z.rem lower prime_pre) = (Z.rem lower prime_pre)) ” &&
  “ ((0 : Int) <= (Z.rem lower prime_pre)) ” &&
  “ ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre)) ” &&
  “ ((Z.rem upper prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < prime_pre) ” &&
  “ (DigitBinomialMachineSafe (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre) ” &&
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (DigitBinomialMachineSafe (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre) ” &&
  “ ((Z.rem upper prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem lower prime_pre)) ”
  &&  emp
)

noncomputable def lucas_theorem_entail_wit_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  (DigitBinomialMachineSafe (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre)

noncomputable def lucas_theorem_entail_wit_2_split_goal_2 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((Z.rem upper prime_pre) < prime_pre)

noncomputable def lucas_theorem_entail_wit_2_split_goal_3 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((0 : Int) <= (Z.rem lower prime_pre))

noncomputable def lucas_theorem_entail_wit_3 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100000) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ (LucasMachineSafe n_pre m_pre prime_pre) ” &&
  “ ((0 : Int) <= (Z.quot lower prime_pre)) ” &&
  “ ((Z.quot lower prime_pre) <= (Z.quot upper prime_pre)) ” &&
  “ ((Z.quot upper prime_pre) <= (n_pre + m_pre)) ” &&
  “ ((n_pre + m_pre) <= 200000) ” &&
  “ ((0 : Int) <= (Z.rem (result * retval) prime_pre)) ” &&
  “ ((Z.rem (result * retval) prime_pre) < prime_pre) ” &&
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (Z.quot upper prime_pre) (Z.quot lower prime_pre) (Z.rem (result * retval) prime_pre)) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (Z.quot upper prime_pre) (Z.quot lower prime_pre) (Z.rem (result * retval) prime_pre)) ” &&
  “ ((Z.rem (result * retval) prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem (result * retval) prime_pre)) ” &&
  “ ((Z.quot upper prime_pre) <= (n_pre + m_pre)) ” &&
  “ ((Z.quot lower prime_pre) <= (Z.quot upper prime_pre)) ” &&
  “ ((0 : Int) <= (Z.quot lower prime_pre)) ”
  &&  emp
)

noncomputable def lucas_theorem_entail_wit_3_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  (LucasProgress (n_pre + m_pre) n_pre prime_pre (Z.quot upper prime_pre) (Z.quot lower prime_pre) (Z.rem (result * retval) prime_pre))

noncomputable def lucas_theorem_entail_wit_3_split_goal_2 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((Z.rem (result * retval) prime_pre) < prime_pre)

noncomputable def lucas_theorem_entail_wit_3_split_goal_3 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((0 : Int) <= (Z.rem (result * retval) prime_pre))

noncomputable def lucas_theorem_entail_wit_3_split_goal_4 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((Z.quot upper prime_pre) <= (n_pre + m_pre))

noncomputable def lucas_theorem_entail_wit_3_split_goal_5 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((Z.quot lower prime_pre) <= (Z.quot upper prime_pre))

noncomputable def lucas_theorem_entail_wit_3_split_goal_6 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre)) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH12 : ((0 : Int) < upper)) (PreH13 : ((0 : Int) <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre))) (PreH16 : ((n_pre + m_pre) <= 200000)) (PreH17 : (upper_digit = (Z.rem upper prime_pre))) (PreH18 : (lower_digit = (Z.rem lower prime_pre))) (PreH19 : ((0 : Int) <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : ((0 : Int) <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH25 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((0 : Int) <= (Z.quot lower prime_pre))

noncomputable def lucas_theorem_return_wit_1 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower <= (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= result) ” &&
  “ (result < prime_pre) ” &&
  “ (LucasBinomialResidue n_pre m_pre prime_pre result) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower <= (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre result) ”
  &&  emp
)

noncomputable def lucas_theorem_return_wit_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower <= (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  (LucasBinomialResidue n_pre m_pre prime_pre result)

noncomputable def lucas_theorem_return_wit_2 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < prime_pre) ” &&
  “ (LucasBinomialResidue n_pre m_pre prime_pre (0 : Int)) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre (0 : Int)) ”
  &&  emp
)

noncomputable def lucas_theorem_return_wit_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre)) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH11 : ((0 : Int) <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre))) (PreH14 : ((n_pre + m_pre) <= 200000)) (PreH15 : ((0 : Int) <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  (LucasBinomialResidue n_pre m_pre prime_pre (0 : Int))

noncomputable def lucas_theorem_partial_solve_wit_1_pure : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH9 : ((0 : Int) < upper)) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre))) (PreH13 : ((n_pre + m_pre) <= 200000)) (PreH14 : (upper_digit = (Z.rem upper prime_pre))) (PreH15 : (lower_digit = (Z.rem lower prime_pre))) (PreH16 : ((0 : Int) <= lower_digit)) (PreH17 : (lower_digit <= upper_digit)) (PreH18 : (upper_digit < prime_pre)) (PreH19 : ((0 : Int) <= result)) (PreH20 : (result < prime_pre)) (PreH21 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH22 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "digit_binomial" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper_digit" ) )) # Int |-> (upper_digit))
  ** ((( &( "lower_digit" ) )) # Int |-> (lower_digit))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_digit) ” &&
  “ (lower_digit <= upper_digit) ” &&
  “ (upper_digit < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (DigitBinomialMachineSafe upper_digit lower_digit prime_pre) ”

noncomputable def lucas_theorem_partial_solve_wit_1_aux : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (upper : Int) (lower : Int) (upper_digit : Int) (lower_digit : Int) (result : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre)) (PreH9 : ((0 : Int) < upper)) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre))) (PreH13 : ((n_pre + m_pre) <= 200000)) (PreH14 : (upper_digit = (Z.rem upper prime_pre))) (PreH15 : (lower_digit = (Z.rem lower prime_pre))) (PreH16 : ((0 : Int) <= lower_digit)) (PreH17 : (lower_digit <= upper_digit)) (PreH18 : (upper_digit < prime_pre)) (PreH19 : ((0 : Int) <= result)) (PreH20 : (result < prime_pre)) (PreH21 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre)) (PreH22 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_digit) ” &&
  “ (lower_digit <= upper_digit) ” &&
  “ (upper_digit < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (DigitBinomialMachineSafe upper_digit lower_digit prime_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100000) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ (LucasMachineSafe n_pre m_pre prime_pre) ” &&
  “ ((0 : Int) < upper) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= upper) ” &&
  “ (upper <= (n_pre + m_pre)) ” &&
  “ ((n_pre + m_pre) <= 200000) ” &&
  “ (upper_digit = (Z.rem upper prime_pre)) ” &&
  “ (lower_digit = (Z.rem lower prime_pre)) ” &&
  “ ((0 : Int) <= lower_digit) ” &&
  “ (lower_digit <= upper_digit) ” &&
  “ (upper_digit < prime_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < prime_pre) ” &&
  “ (DigitBinomialMachineSafe upper_digit lower_digit prime_pre) ” &&
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result) ”
  &&  emp

noncomputable def lucas_theorem_partial_solve_wit_1 : Prop := lucas_theorem_partial_solve_wit_1_pure -> lucas_theorem_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_binomial_digit_mod_prime_safety_wit_1 : binomial_digit_mod_prime_safety_wit_1
  proof_of_binomial_digit_mod_prime_safety_wit_2 : binomial_digit_mod_prime_safety_wit_2
  proof_of_binomial_digit_mod_prime_safety_wit_3 : binomial_digit_mod_prime_safety_wit_3
  proof_of_binomial_digit_mod_prime_safety_wit_4 : binomial_digit_mod_prime_safety_wit_4
  proof_of_binomial_digit_mod_prime_safety_wit_5 : binomial_digit_mod_prime_safety_wit_5
  proof_of_binomial_digit_mod_prime_safety_wit_6 : binomial_digit_mod_prime_safety_wit_6
  proof_of_binomial_digit_mod_prime_safety_wit_7 : binomial_digit_mod_prime_safety_wit_7
  proof_of_binomial_digit_mod_prime_safety_wit_8 : binomial_digit_mod_prime_safety_wit_8
  proof_of_binomial_digit_mod_prime_safety_wit_9 : binomial_digit_mod_prime_safety_wit_9
  proof_of_binomial_digit_mod_prime_safety_wit_10 : binomial_digit_mod_prime_safety_wit_10
  proof_of_binomial_digit_mod_prime_safety_wit_11 : binomial_digit_mod_prime_safety_wit_11
  proof_of_binomial_digit_mod_prime_safety_wit_12 : binomial_digit_mod_prime_safety_wit_12
  proof_of_binomial_digit_mod_prime_safety_wit_13 : binomial_digit_mod_prime_safety_wit_13
  proof_of_binomial_digit_mod_prime_safety_wit_18 : binomial_digit_mod_prime_safety_wit_18
  proof_of_binomial_digit_mod_prime_safety_wit_19 : binomial_digit_mod_prime_safety_wit_19
  proof_of_binomial_digit_mod_prime_safety_wit_20 : binomial_digit_mod_prime_safety_wit_20
  proof_of_binomial_digit_mod_prime_safety_wit_21 : binomial_digit_mod_prime_safety_wit_21
  proof_of_binomial_digit_mod_prime_safety_wit_22 : binomial_digit_mod_prime_safety_wit_22
  proof_of_binomial_digit_mod_prime_safety_wit_23 : binomial_digit_mod_prime_safety_wit_23
  proof_of_binomial_digit_mod_prime_safety_wit_24 : binomial_digit_mod_prime_safety_wit_24
  proof_of_binomial_digit_mod_prime_safety_wit_25 : binomial_digit_mod_prime_safety_wit_25
  proof_of_binomial_digit_mod_prime_safety_wit_26 : binomial_digit_mod_prime_safety_wit_26
  proof_of_binomial_digit_mod_prime_safety_wit_27 : binomial_digit_mod_prime_safety_wit_27
  proof_of_binomial_digit_mod_prime_safety_wit_30 : binomial_digit_mod_prime_safety_wit_30
  proof_of_binomial_digit_mod_prime_safety_wit_31 : binomial_digit_mod_prime_safety_wit_31
  proof_of_binomial_digit_mod_prime_partial_solve_wit_1_pure : binomial_digit_mod_prime_partial_solve_wit_1_pure
  proof_of_binomial_digit_mod_prime_partial_solve_wit_1 : binomial_digit_mod_prime_partial_solve_wit_1
  proof_of_binomial_digit_mod_prime_partial_solve_wit_2_pure : binomial_digit_mod_prime_partial_solve_wit_2_pure
  proof_of_binomial_digit_mod_prime_partial_solve_wit_2 : binomial_digit_mod_prime_partial_solve_wit_2
  proof_of_lucas_theorem_safety_wit_1 : lucas_theorem_safety_wit_1
  proof_of_lucas_theorem_safety_wit_2 : lucas_theorem_safety_wit_2
  proof_of_lucas_theorem_safety_wit_3 : lucas_theorem_safety_wit_3
  proof_of_lucas_theorem_safety_wit_4 : lucas_theorem_safety_wit_4
  proof_of_lucas_theorem_safety_wit_5 : lucas_theorem_safety_wit_5
  proof_of_lucas_theorem_safety_wit_6 : lucas_theorem_safety_wit_6
  proof_of_lucas_theorem_safety_wit_7 : lucas_theorem_safety_wit_7
  proof_of_lucas_theorem_safety_wit_8 : lucas_theorem_safety_wit_8
  proof_of_lucas_theorem_safety_wit_10 : lucas_theorem_safety_wit_10
  proof_of_lucas_theorem_safety_wit_11 : lucas_theorem_safety_wit_11
  proof_of_lucas_theorem_safety_wit_12 : lucas_theorem_safety_wit_12
  proof_of_lucas_theorem_partial_solve_wit_1_pure : lucas_theorem_partial_solve_wit_1_pure
  proof_of_lucas_theorem_partial_solve_wit_1 : lucas_theorem_partial_solve_wit_1
  proof_of_binomial_digit_mod_prime_safety_wit_14 : binomial_digit_mod_prime_safety_wit_14
  proof_of_binomial_digit_mod_prime_safety_wit_15 : binomial_digit_mod_prime_safety_wit_15
  proof_of_binomial_digit_mod_prime_safety_wit_16 : binomial_digit_mod_prime_safety_wit_16
  proof_of_binomial_digit_mod_prime_safety_wit_17 : binomial_digit_mod_prime_safety_wit_17
  proof_of_binomial_digit_mod_prime_safety_wit_28 : binomial_digit_mod_prime_safety_wit_28
  proof_of_binomial_digit_mod_prime_safety_wit_29 : binomial_digit_mod_prime_safety_wit_29
  proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1
  proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2
  proof_of_binomial_digit_mod_prime_entail_wit_2_1 : binomial_digit_mod_prime_entail_wit_2_1
  proof_of_binomial_digit_mod_prime_entail_wit_2_2 : binomial_digit_mod_prime_entail_wit_2_2
  proof_of_binomial_digit_mod_prime_entail_wit_3_1 : binomial_digit_mod_prime_entail_wit_3_1
  proof_of_binomial_digit_mod_prime_entail_wit_3_2 : binomial_digit_mod_prime_entail_wit_3_2
  proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1
  proof_of_binomial_digit_mod_prime_return_wit_2 : binomial_digit_mod_prime_return_wit_2
  proof_of_lucas_theorem_safety_wit_9 : lucas_theorem_safety_wit_9
  proof_of_lucas_theorem_entail_wit_1 : lucas_theorem_entail_wit_1
  proof_of_lucas_theorem_entail_wit_2 : lucas_theorem_entail_wit_2
  proof_of_lucas_theorem_entail_wit_3 : lucas_theorem_entail_wit_3
  proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1
  proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2

end Algorithms.lucas_theorem.lean.groundtruth.lucas_theorem_goal
