import SimpleC.SL.SeparationLogic

import Algorithms.modular_power.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.modular_power.lean.groundtruth.modular_power_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance modular_power_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def modular_power_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_power_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) (PreH6 : ((0 : Int) <= a)) (PreH7 : (a < modulus_pre)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= b_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < modulus_pre)) (PreH12 : ((0 : Int) <= (a * a))) (PreH13 : ((a * a) <= INT_MAX)) (PreH14 : ((0 : Int) <= (result * a))) (PreH15 : ((result * a) <= INT_MAX)) (PreH16 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_power_safety_wit_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) <= a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((0 : Int) <= b_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= a)) (PreH8 : (a < modulus_pre)) (PreH9 : ((0 : Int) <= b)) (PreH10 : (b <= b_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (a * a))) (PreH14 : ((a * a) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * a))) (PreH16 : ((result * a) <= INT_MAX)) (PreH17 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) <= a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((0 : Int) <= b_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= a)) (PreH8 : (a < modulus_pre)) (PreH9 : ((0 : Int) <= b)) (PreH10 : (b <= b_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (a * a))) (PreH14 : ((a * a) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * a))) (PreH16 : ((result * a) <= INT_MAX)) (PreH17 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_safety_wit_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) <= a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((0 : Int) <= b_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= a)) (PreH8 : (a < modulus_pre)) (PreH9 : ((0 : Int) <= b)) (PreH10 : (b <= b_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (a * a))) (PreH14 : ((a * a) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * a))) (PreH16 : ((result * a) <= INT_MAX)) (PreH17 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_power_safety_wit_6 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((result * a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_7 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result * a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result * a)) ”

noncomputable def modular_power_safety_wit_8 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * a) modulus_pre)))
|--
  “ (((a * a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_9 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * a) modulus_pre)))
|--
  “ ((a * a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a * a)) ”

noncomputable def modular_power_safety_wit_10 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((a * a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_11 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((a * a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a * a)) ”

noncomputable def modular_power_safety_wit_12 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((Z.rem (a * a) modulus_pre)))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * a) modulus_pre)))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_13 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((Z.rem (a * a) modulus_pre)))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * a) modulus_pre)))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_safety_wit_14 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((Z.rem (a * a) modulus_pre)))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_15 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((Z.rem (a * a) modulus_pre)))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_entail_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  TT && emp 
|--
  “ ((0 : Int) <= a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ (b_pre <= b_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < modulus_pre) ” &&
  “ ((0 : Int) <= (a_pre * a_pre)) ” &&
  “ ((a_pre * a_pre) <= INT_MAX) ” &&
  “ ((0 : Int) <= (1 * a_pre)) ” &&
  “ ((1 * a_pre) <= INT_MAX) ” &&
  “ (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1)

noncomputable def modular_power_entail_wit_2_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) <= (Z.rem (a * a) modulus_pre)) ” &&
  “ ((Z.rem (a * a) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.quot b 2) <= b_pre) ” &&
  “ ((0 : Int) <= (Z.rem (result * a) modulus_pre)) ” &&
  “ ((Z.rem (result * a) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= ((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre))) ” &&
  “ (((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (result * a) modulus_pre) * (Z.rem (a * a) modulus_pre))) ” &&
  “ (((Z.rem (result * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ (ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a * a) modulus_pre) (Z.quot b 2) (Z.rem (result * a) modulus_pre)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a * a) modulus_pre) (Z.quot b 2) (Z.rem (result * a) modulus_pre)) ” &&
  “ (((Z.rem (result * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (result * a) modulus_pre) * (Z.rem (a * a) modulus_pre))) ” &&
  “ (((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre))) ” &&
  “ ((Z.rem (result * a) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem (result * a) modulus_pre)) ” &&
  “ ((Z.quot b 2) <= b_pre) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.rem (a * a) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem (a * a) modulus_pre)) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_2_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a * a) modulus_pre) (Z.quot b 2) (Z.rem (result * a) modulus_pre))

noncomputable def modular_power_entail_wit_2_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (((Z.rem (result * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_1_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= ((Z.rem (result * a) modulus_pre) * (Z.rem (a * a) modulus_pre)))

noncomputable def modular_power_entail_wit_2_1_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_1_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= ((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)))

noncomputable def modular_power_entail_wit_2_1_split_goal_6 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((Z.rem (result * a) modulus_pre) < modulus_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_7 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (Z.rem (result * a) modulus_pre))

noncomputable def modular_power_entail_wit_2_1_split_goal_8 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((Z.quot b 2) <= b_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_9 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_power_entail_wit_2_1_split_goal_10 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((Z.rem (a * a) modulus_pre) < modulus_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_11 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (Z.rem (a * a) modulus_pre))

noncomputable def modular_power_entail_wit_2_2 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) <= (Z.rem (a * a) modulus_pre)) ” &&
  “ ((Z.rem (a * a) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.quot b 2) <= b_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < modulus_pre) ” &&
  “ ((0 : Int) <= ((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre))) ” &&
  “ (((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= (result * (Z.rem (a * a) modulus_pre))) ” &&
  “ ((result * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ (ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a * a) modulus_pre) (Z.quot b 2) result) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a * a) modulus_pre) (Z.quot b 2) result) ” &&
  “ ((result * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= (result * (Z.rem (a * a) modulus_pre))) ” &&
  “ (((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre))) ” &&
  “ ((Z.quot b 2) <= b_pre) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.rem (a * a) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem (a * a) modulus_pre)) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_2_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a * a) modulus_pre) (Z.quot b 2) result)

noncomputable def modular_power_entail_wit_2_2_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((result * (Z.rem (a * a) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_2_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (result * (Z.rem (a * a) modulus_pre)))

noncomputable def modular_power_entail_wit_2_2_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_2_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= ((Z.rem (a * a) modulus_pre) * (Z.rem (a * a) modulus_pre)))

noncomputable def modular_power_entail_wit_2_2_split_goal_6 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((Z.quot b 2) <= b_pre)

noncomputable def modular_power_entail_wit_2_2_split_goal_7 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_power_entail_wit_2_2_split_goal_8 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((Z.rem (a * a) modulus_pre) < modulus_pre)

noncomputable def modular_power_entail_wit_2_2_split_goal_9 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) <= a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : ((0 : Int) <= b_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b <= b_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (a * a))) (PreH15 : ((a * a) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * a))) (PreH17 : ((result * a) <= INT_MAX)) (PreH18 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (Z.rem (a * a) modulus_pre))

noncomputable def modular_power_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) <= a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((0 : Int) <= b_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= a)) (PreH8 : (a < modulus_pre)) (PreH9 : ((0 : Int) <= b)) (PreH10 : (b <= b_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (a * a))) (PreH14 : ((a * a) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * a))) (PreH16 : ((result * a) <= INT_MAX)) (PreH17 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= result) ” &&
  “ (result < modulus_pre) ” &&
  “ (ModularPower a_pre b_pre modulus_pre result) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) <= a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((0 : Int) <= b_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= a)) (PreH8 : (a < modulus_pre)) (PreH9 : ((0 : Int) <= b)) (PreH10 : (b <= b_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (a * a))) (PreH14 : ((a * a) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * a))) (PreH16 : ((result * a) <= INT_MAX)) (PreH17 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (ModularPower a_pre b_pre modulus_pre result) ”
  &&  emp
)

noncomputable def modular_power_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) <= a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((0 : Int) <= b_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= a)) (PreH8 : (a < modulus_pre)) (PreH9 : ((0 : Int) <= b)) (PreH10 : (b <= b_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (a * a))) (PreH14 : ((a * a) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * a))) (PreH16 : ((result * a) <= INT_MAX)) (PreH17 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (ModularPower a_pre b_pre modulus_pre result)


structure VC_Correct : Type where
  proof_of_modular_power_safety_wit_1 : modular_power_safety_wit_1
  proof_of_modular_power_safety_wit_2 : modular_power_safety_wit_2
  proof_of_modular_power_safety_wit_3 : modular_power_safety_wit_3
  proof_of_modular_power_safety_wit_4 : modular_power_safety_wit_4
  proof_of_modular_power_safety_wit_5 : modular_power_safety_wit_5
  proof_of_modular_power_safety_wit_6 : modular_power_safety_wit_6
  proof_of_modular_power_safety_wit_7 : modular_power_safety_wit_7
  proof_of_modular_power_safety_wit_8 : modular_power_safety_wit_8
  proof_of_modular_power_safety_wit_9 : modular_power_safety_wit_9
  proof_of_modular_power_safety_wit_10 : modular_power_safety_wit_10
  proof_of_modular_power_safety_wit_11 : modular_power_safety_wit_11
  proof_of_modular_power_safety_wit_12 : modular_power_safety_wit_12
  proof_of_modular_power_safety_wit_13 : modular_power_safety_wit_13
  proof_of_modular_power_safety_wit_14 : modular_power_safety_wit_14
  proof_of_modular_power_safety_wit_15 : modular_power_safety_wit_15
  proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1
  proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1
  proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2
  proof_of_modular_power_return_wit_1 : modular_power_return_wit_1

end Algorithms.modular_power.lean.groundtruth.modular_power_goal
