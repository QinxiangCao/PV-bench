import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance euler_theorem_inverse_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def euler_phi_safety_wit_1 : Prop :=
  forall (value_pre : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  ((( &( "factor" ) )) # Int |->_)
  ** ((( &( "result" ) )) # Int |-> (value_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def euler_phi_safety_wit_2 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((0 : Int) <= (factor * factor))) (PreH10 : ((factor * factor) <= INT_MAX)) (PreH11 : (EulerPhiProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((factor * factor) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (factor * factor)) ”

noncomputable def euler_phi_safety_wit_3 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((factor * factor) <= value)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : ((0 : Int) <= (factor * factor))) (PreH11 : ((factor * factor) <= INT_MAX)) (PreH12 : (EulerPhiProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((value ≠ (INT_MIN)) ∨ (factor ≠ (-1))) ” &&
  “ (factor ≠ (0 : Int)) ”

noncomputable def euler_phi_safety_wit_4 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((factor * factor) <= value)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : ((0 : Int) <= (factor * factor))) (PreH11 : ((factor * factor) <= INT_MAX)) (PreH12 : (EulerPhiProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def euler_phi_safety_wit_5 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((value ≠ (INT_MIN)) ∨ (factor ≠ (-1))) ” &&
  “ (factor ≠ (0 : Int)) ”

noncomputable def euler_phi_safety_wit_6 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def euler_phi_safety_wit_7 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((value ≠ (INT_MIN)) ∨ (factor ≠ (-1))) ” &&
  “ (factor ≠ (0 : Int)) ”

noncomputable def euler_phi_safety_wit_8 : Prop :=
  forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ (((Z.quot result factor) * (factor - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot result factor) * (factor - 1))) ”

noncomputable def euler_phi_safety_wit_9 : Prop :=
  forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((factor - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (factor - 1)) ”

noncomputable def euler_phi_safety_wit_10 : Prop :=
  forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((result ≠ (INT_MIN)) ∨ (factor ≠ (-1))) ” &&
  “ (factor ≠ (0 : Int)) ”

noncomputable def euler_phi_safety_wit_11 : Prop :=
  forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def euler_phi_safety_wit_12 : Prop :=
  forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (((Z.quot result factor) * (factor - 1))))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((factor + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (factor + 1)) ”

noncomputable def euler_phi_safety_wit_13 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : ((factor * factor) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : ((0 : Int) <= (factor * factor))) (PreH12 : ((factor * factor) <= INT_MAX)) (PreH13 : (EulerPhiProgress value_pre factor value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** ((( &( "factor" ) )) # Int |-> (factor))
|--
  “ ((factor + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (factor + 1)) ”

noncomputable def euler_phi_safety_wit_14 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= frontier)) (PreH8 : (frontier <= 216)) (PreH9 : ((0 : Int) <= (frontier * frontier))) (PreH10 : ((frontier * frontier) <= INT_MAX)) (PreH11 : ((frontier * frontier) > value)) (PreH12 : ((Z.rem result value) = (0 : Int))) (PreH13 : (1 <= (Z.quot result value))) (PreH14 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH15 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH16 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH17 : (EulerPhiProgress value_pre frontier value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def euler_phi_safety_wit_15 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= frontier)) (PreH8 : (frontier <= 216)) (PreH9 : ((0 : Int) <= (frontier * frontier))) (PreH10 : ((frontier * frontier) <= INT_MAX)) (PreH11 : ((frontier * frontier) > value)) (PreH12 : (value = 1)) (PreH13 : (EulerPhiProgress value_pre frontier value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def euler_phi_safety_wit_16 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : (value = 1)) (PreH14 : (EulerPhiProgress value_pre frontier value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ False ”

noncomputable def euler_phi_safety_wit_17 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((Z.quot result value) * (value - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot result value) * (value - 1))) ”

noncomputable def euler_phi_safety_wit_18 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((value - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (value - 1)) ”

noncomputable def euler_phi_safety_wit_19 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result ≠ (INT_MIN)) ∨ (value ≠ (-1))) ” &&
  “ (value ≠ (0 : Int)) ”

noncomputable def euler_phi_safety_wit_20 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def euler_phi_entail_wit_1 : Prop :=
  (
forall (value_pre : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= value_pre) ” &&
  “ (value_pre <= value_pre) ” &&
  “ (1 <= value_pre) ” &&
  “ (value_pre <= value_pre) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= 216) ” &&
  “ ((0 : Int) <= (2 * 2)) ” &&
  “ ((2 * 2) <= INT_MAX) ” &&
  “ (EulerPhiProgress value_pre 2 value_pre value_pre) ”
  &&  emp
) \/
(
forall (value_pre : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  TT && emp 
|--
  “ (EulerPhiProgress value_pre 2 value_pre value_pre) ”
  &&  emp
)

noncomputable def euler_phi_entail_wit_1_split_goal_1 : Prop :=
  forall (value_pre : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  (EulerPhiProgress value_pre 2 value_pre value_pre)

noncomputable def euler_phi_entail_wit_2 : Prop :=
  (
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : ((factor * factor) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : ((0 : Int) <= (factor * factor))) (PreH12 : ((factor * factor) <= INT_MAX)) (PreH13 : (EulerPhiProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= value) ” &&
  “ (value <= value_pre) ” &&
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (2 <= factor) ” &&
  “ (factor <= 216) ” &&
  “ (EulerPhiRemovalProgress value_pre factor value result) ”
  &&  emp
) \/
(
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : ((factor * factor) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : ((0 : Int) <= (factor * factor))) (PreH12 : ((factor * factor) <= INT_MAX)) (PreH13 : (EulerPhiProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (EulerPhiRemovalProgress value_pre factor value result) ”
  &&  emp
)

noncomputable def euler_phi_entail_wit_2_split_goal_1 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : ((factor * factor) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : ((0 : Int) <= (factor * factor))) (PreH12 : ((factor * factor) <= INT_MAX)) (PreH13 : (EulerPhiProgress value_pre factor value result)) ,
  (EulerPhiRemovalProgress value_pre factor value result)

noncomputable def euler_phi_entail_wit_3 : Prop :=
  (
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= (Z.quot value factor)) ” &&
  “ ((Z.quot value factor) <= value_pre) ” &&
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (2 <= factor) ” &&
  “ (factor <= 216) ” &&
  “ (EulerPhiRemovalProgress value_pre factor (Z.quot value factor) result) ”
  &&  emp
) \/
(
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (EulerPhiRemovalProgress value_pre factor (Z.quot value factor) result) ” &&
  “ ((Z.quot value factor) <= value_pre) ” &&
  “ (1 <= (Z.quot value factor)) ”
  &&  emp
)

noncomputable def euler_phi_entail_wit_3_split_goal_1 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  (EulerPhiRemovalProgress value_pre factor (Z.quot value factor) result)

noncomputable def euler_phi_entail_wit_3_split_goal_2 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((Z.quot value factor) <= value_pre)

noncomputable def euler_phi_entail_wit_3_split_goal_3 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) = (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  (1 <= (Z.quot value factor))

noncomputable def euler_phi_entail_wit_4 : Prop :=
  (
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= value) ” &&
  “ (value <= value_pre) ” &&
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (2 <= factor) ” &&
  “ (factor <= 216) ” &&
  “ ((Z.rem value factor) ≠ (0 : Int)) ” &&
  “ ((Z.rem result factor) = (0 : Int)) ” &&
  “ (1 <= (Z.quot result factor)) ” &&
  “ ((0 : Int) <= ((Z.quot result factor) * (factor - 1))) ” &&
  “ (((Z.quot result factor) * (factor - 1)) <= value_pre) ” &&
  “ (((Z.quot result factor) * (factor - 1)) <= INT_MAX) ” &&
  “ (EulerPhiRemovalProgress value_pre factor value result) ”
  &&  emp
) \/
(
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (((Z.quot result factor) * (factor - 1)) <= INT_MAX) ” &&
  “ (((Z.quot result factor) * (factor - 1)) <= value_pre) ” &&
  “ ((0 : Int) <= ((Z.quot result factor) * (factor - 1))) ” &&
  “ (1 <= (Z.quot result factor)) ” &&
  “ ((Z.rem result factor) = (0 : Int)) ”
  &&  emp
)

noncomputable def euler_phi_entail_wit_4_split_goal_1 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  (((Z.quot result factor) * (factor - 1)) <= INT_MAX)

noncomputable def euler_phi_entail_wit_4_split_goal_2 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  (((Z.quot result factor) * (factor - 1)) <= value_pre)

noncomputable def euler_phi_entail_wit_4_split_goal_3 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))

noncomputable def euler_phi_entail_wit_4_split_goal_4 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  (1 <= (Z.quot result factor))

noncomputable def euler_phi_entail_wit_4_split_goal_5 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((Z.rem result factor) = (0 : Int))

noncomputable def euler_phi_entail_wit_5_1 : Prop :=
  (
forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= value) ” &&
  “ (value <= value_pre) ” &&
  “ (1 <= ((Z.quot result factor) * (factor - 1))) ” &&
  “ (((Z.quot result factor) * (factor - 1)) <= value_pre) ” &&
  “ (2 <= (factor + 1)) ” &&
  “ ((factor + 1) <= 216) ” &&
  “ ((0 : Int) <= ((factor + 1) * (factor + 1))) ” &&
  “ (((factor + 1) * (factor + 1)) <= INT_MAX) ” &&
  “ (EulerPhiProgress value_pre (factor + 1) value ((Z.quot result factor) * (factor - 1))) ”
  &&  emp
) \/
(
forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (EulerPhiProgress value_pre (factor + 1) value ((Z.quot result factor) * (factor - 1))) ” &&
  “ ((factor + 1) <= 216) ”
  &&  emp
)

noncomputable def euler_phi_entail_wit_5_1_split_goal_1 : Prop :=
  forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  (EulerPhiProgress value_pre (factor + 1) value ((Z.quot result factor) * (factor - 1)))

noncomputable def euler_phi_entail_wit_5_1_split_goal_2 : Prop :=
  forall (value_pre : Int) (value : Int) (result : Int) (factor : Int) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : ((Z.rem value factor) ≠ (0 : Int))) (PreH10 : ((Z.rem result factor) = (0 : Int))) (PreH11 : (1 <= (Z.quot result factor))) (PreH12 : ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) (PreH13 : (((Z.quot result factor) * (factor - 1)) <= value_pre)) (PreH14 : (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) (PreH15 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((factor + 1) <= 216)

noncomputable def euler_phi_entail_wit_5_2 : Prop :=
  (
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : ((factor * factor) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : ((0 : Int) <= (factor * factor))) (PreH12 : ((factor * factor) <= INT_MAX)) (PreH13 : (EulerPhiProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= value) ” &&
  “ (value <= value_pre) ” &&
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (2 <= (factor + 1)) ” &&
  “ ((factor + 1) <= 216) ” &&
  “ ((0 : Int) <= ((factor + 1) * (factor + 1))) ” &&
  “ (((factor + 1) * (factor + 1)) <= INT_MAX) ” &&
  “ (EulerPhiProgress value_pre (factor + 1) value result) ”
  &&  emp
) \/
(
forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : ((factor * factor) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : ((0 : Int) <= (factor * factor))) (PreH12 : ((factor * factor) <= INT_MAX)) (PreH13 : (EulerPhiProgress value_pre factor value result)) ,
  TT && emp 
|--
  “ (EulerPhiProgress value_pre (factor + 1) value result) ”
  &&  emp
)

noncomputable def euler_phi_entail_wit_5_2_split_goal_1 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : ((factor * factor) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : ((0 : Int) <= (factor * factor))) (PreH12 : ((factor * factor) <= INT_MAX)) (PreH13 : (EulerPhiProgress value_pre factor value result)) ,
  (EulerPhiProgress value_pre (factor + 1) value result)

noncomputable def euler_phi_entail_wit_6 : Prop :=
  forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((factor * factor) > value)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : ((0 : Int) <= (factor * factor))) (PreH11 : ((factor * factor) <= INT_MAX)) (PreH12 : (EulerPhiProgress value_pre factor value result)) ,
  TT && emp 
|--
  (EX frontier : Int,
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= value) ” &&
  “ (value <= value_pre) ” &&
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (2 <= frontier) ” &&
  “ (frontier <= 216) ” &&
  “ ((0 : Int) <= (frontier * frontier)) ” &&
  “ ((frontier * frontier) <= INT_MAX) ” &&
  “ ((frontier * frontier) > value) ” &&
  “ ((Z.rem result value) = (0 : Int)) ” &&
  “ (1 <= (Z.quot result value)) ” &&
  “ ((0 : Int) <= ((Z.quot result value) * (value - 1))) ” &&
  “ (((Z.quot result value) * (value - 1)) <= value_pre) ” &&
  “ (((Z.quot result value) * (value - 1)) <= INT_MAX) ” &&
  “ (EulerPhiProgress value_pre frontier value result) ”
  &&  emp)
  ||
  (EX frontier : Int,
  “ (2 <= value_pre) ” &&
  “ (value_pre <= 46341) ” &&
  “ (1 <= value) ” &&
  “ (value <= value_pre) ” &&
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (2 <= frontier) ” &&
  “ (frontier <= 216) ” &&
  “ ((0 : Int) <= (frontier * frontier)) ” &&
  “ ((frontier * frontier) <= INT_MAX) ” &&
  “ ((frontier * frontier) > value) ” &&
  “ (value = 1) ” &&
  “ (EulerPhiProgress value_pre frontier value result) ”
  &&  emp)

noncomputable def euler_phi_return_wit_1 : Prop :=
  (
forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  TT && emp 
|--
  “ (1 <= ((Z.quot result value) * (value - 1))) ” &&
  “ (((Z.quot result value) * (value - 1)) <= value_pre) ” &&
  “ (EulerPhi value_pre ((Z.quot result value) * (value - 1))) ”
  &&  emp
) \/
(
forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  TT && emp 
|--
  “ (EulerPhi value_pre ((Z.quot result value) * (value - 1))) ”
  &&  emp
)

noncomputable def euler_phi_return_wit_1_split_goal_1 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value ≠ 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  (EulerPhi value_pre ((Z.quot result value) * (value - 1)))

noncomputable def euler_phi_return_wit_2 : Prop :=
  (
forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  TT && emp 
|--
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (EulerPhi value_pre result) ”
  &&  emp
) \/
(
forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  TT && emp 
|--
  “ (EulerPhi value_pre result) ”
  &&  emp
)

noncomputable def euler_phi_return_wit_2_split_goal_1 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : ((Z.rem result value) = (0 : Int))) (PreH14 : (1 <= (Z.quot result value))) (PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1)))) (PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre)) (PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX)) (PreH18 : (EulerPhiProgress value_pre frontier value result)) ,
  (EulerPhi value_pre result)

noncomputable def euler_phi_return_wit_3 : Prop :=
  (
forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : (value = 1)) (PreH14 : (EulerPhiProgress value_pre frontier value result)) ,
  TT && emp 
|--
  “ (1 <= result) ” &&
  “ (result <= value_pre) ” &&
  “ (EulerPhi value_pre result) ”
  &&  emp
) \/
(
forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : (value = 1)) (PreH14 : (EulerPhiProgress value_pre frontier value result)) ,
  TT && emp 
|--
  “ (EulerPhi value_pre result) ”
  &&  emp
)

noncomputable def euler_phi_return_wit_3_split_goal_1 : Prop :=
  forall (value_pre : Int) (frontier : Int) (value : Int) (result : Int) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((0 : Int) <= (frontier * frontier))) (PreH11 : ((frontier * frontier) <= INT_MAX)) (PreH12 : ((frontier * frontier) > value)) (PreH13 : (value = 1)) (PreH14 : (EulerPhiProgress value_pre frontier value result)) ,
  (EulerPhi value_pre result)

noncomputable def modular_power_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (PreH1 : ((0 : Int) <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : ((0 : Int) <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "base" ) )) # Int |-> (base_pre))
  ** ((( &( "exponent" ) )) # Int |-> (exponent_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_power_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((0 : Int) <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : ((0 : Int) <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base < modulus_pre)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= exponent_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < modulus_pre)) (PreH12 : ((0 : Int) <= (base * base))) (PreH13 : ((base * base) <= INT_MAX)) (PreH14 : ((0 : Int) <= (result * base))) (PreH15 : ((result * base) <= INT_MAX)) (PreH16 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_power_safety_wit_3 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : (exponent > (0 : Int))) (PreH2 : ((0 : Int) <= base_pre)) (PreH3 : (base_pre < modulus_pre)) (PreH4 : ((0 : Int) <= exponent_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= base)) (PreH8 : (base < modulus_pre)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent <= exponent_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (base * base))) (PreH14 : ((base * base) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * base))) (PreH16 : ((result * base) <= INT_MAX)) (PreH17 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((exponent ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_4 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : (exponent > (0 : Int))) (PreH2 : ((0 : Int) <= base_pre)) (PreH3 : (base_pre < modulus_pre)) (PreH4 : ((0 : Int) <= exponent_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= base)) (PreH8 : (base < modulus_pre)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent <= exponent_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (base * base))) (PreH14 : ((base * base) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * base))) (PreH16 : ((result * base) <= INT_MAX)) (PreH17 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_safety_wit_5 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : (exponent > (0 : Int))) (PreH2 : ((0 : Int) <= base_pre)) (PreH3 : (base_pre < modulus_pre)) (PreH4 : ((0 : Int) <= exponent_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= base)) (PreH8 : (base < modulus_pre)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent <= exponent_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (base * base))) (PreH14 : ((base * base) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * base))) (PreH16 : ((result * base) <= INT_MAX)) (PreH17 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_power_safety_wit_6 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((result * base) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_7 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result * base) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result * base)) ”

noncomputable def modular_power_safety_wit_8 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * base) modulus_pre)))
|--
  “ (((base * base) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_9 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * base) modulus_pre)))
|--
  “ ((base * base) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (base * base)) ”

noncomputable def modular_power_safety_wit_10 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((base * base) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_11 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> (base))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((base * base) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (base * base)) ”

noncomputable def modular_power_safety_wit_12 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> ((Z.rem (base * base) modulus_pre)))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * base) modulus_pre)))
|--
  “ ((exponent ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_13 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> ((Z.rem (base * base) modulus_pre)))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result * base) modulus_pre)))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_safety_wit_14 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> ((Z.rem (base * base) modulus_pre)))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((exponent ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_15 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "base" ) )) # Int |-> ((Z.rem (base * base) modulus_pre)))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_entail_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (PreH1 : ((0 : Int) <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : ((0 : Int) <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  TT && emp 
|--
  “ ((0 : Int) <= base_pre) ” &&
  “ (base_pre < modulus_pre) ” &&
  “ ((0 : Int) <= exponent_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) <= base_pre) ” &&
  “ (base_pre < modulus_pre) ” &&
  “ ((0 : Int) <= exponent_pre) ” &&
  “ (exponent_pre <= exponent_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < modulus_pre) ” &&
  “ ((0 : Int) <= (base_pre * base_pre)) ” &&
  “ ((base_pre * base_pre) <= INT_MAX) ” &&
  “ ((0 : Int) <= (1 * base_pre)) ” &&
  “ ((1 * base_pre) <= INT_MAX) ” &&
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre base_pre exponent_pre 1) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (PreH1 : ((0 : Int) <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : ((0 : Int) <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  TT && emp 
|--
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre base_pre exponent_pre 1) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (PreH1 : ((0 : Int) <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : ((0 : Int) <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  (EulerModularPowerProgress base_pre exponent_pre modulus_pre base_pre exponent_pre 1)

noncomputable def modular_power_entail_wit_2_1 : Prop :=
  (
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= base_pre) ” &&
  “ (base_pre < modulus_pre) ” &&
  “ ((0 : Int) <= exponent_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) <= (Z.rem (base * base) modulus_pre)) ” &&
  “ ((Z.rem (base * base) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.quot exponent 2)) ” &&
  “ ((Z.quot exponent 2) <= exponent_pre) ” &&
  “ ((0 : Int) <= (Z.rem (result * base) modulus_pre)) ” &&
  “ ((Z.rem (result * base) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= ((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre))) ” &&
  “ (((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (result * base) modulus_pre) * (Z.rem (base * base) modulus_pre))) ” &&
  “ (((Z.rem (result * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre (Z.rem (base * base) modulus_pre) (Z.quot exponent 2) (Z.rem (result * base) modulus_pre)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  TT && emp 
|--
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre (Z.rem (base * base) modulus_pre) (Z.quot exponent 2) (Z.rem (result * base) modulus_pre)) ” &&
  “ (((Z.rem (result * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (result * base) modulus_pre) * (Z.rem (base * base) modulus_pre))) ” &&
  “ (((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre))) ” &&
  “ ((Z.rem (result * base) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem (result * base) modulus_pre)) ” &&
  “ ((Z.quot exponent 2) <= exponent_pre) ” &&
  “ ((0 : Int) <= (Z.quot exponent 2)) ” &&
  “ ((Z.rem (base * base) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem (base * base) modulus_pre)) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_2_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  (EulerModularPowerProgress base_pre exponent_pre modulus_pre (Z.rem (base * base) modulus_pre) (Z.quot exponent 2) (Z.rem (result * base) modulus_pre))

noncomputable def modular_power_entail_wit_2_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  (((Z.rem (result * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_1_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= ((Z.rem (result * base) modulus_pre) * (Z.rem (base * base) modulus_pre)))

noncomputable def modular_power_entail_wit_2_1_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  (((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_1_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= ((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)))

noncomputable def modular_power_entail_wit_2_1_split_goal_6 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((Z.rem (result * base) modulus_pre) < modulus_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_7 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= (Z.rem (result * base) modulus_pre))

noncomputable def modular_power_entail_wit_2_1_split_goal_8 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((Z.quot exponent 2) <= exponent_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_9 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= (Z.quot exponent 2))

noncomputable def modular_power_entail_wit_2_1_split_goal_10 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((Z.rem (base * base) modulus_pre) < modulus_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_11 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) = 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= (Z.rem (base * base) modulus_pre))

noncomputable def modular_power_entail_wit_2_2 : Prop :=
  (
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= base_pre) ” &&
  “ (base_pre < modulus_pre) ” &&
  “ ((0 : Int) <= exponent_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) <= (Z.rem (base * base) modulus_pre)) ” &&
  “ ((Z.rem (base * base) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.quot exponent 2)) ” &&
  “ ((Z.quot exponent 2) <= exponent_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < modulus_pre) ” &&
  “ ((0 : Int) <= ((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre))) ” &&
  “ (((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= (result * (Z.rem (base * base) modulus_pre))) ” &&
  “ ((result * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre (Z.rem (base * base) modulus_pre) (Z.quot exponent 2) result) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  TT && emp 
|--
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre (Z.rem (base * base) modulus_pre) (Z.quot exponent 2) result) ” &&
  “ ((result * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= (result * (Z.rem (base * base) modulus_pre))) ” &&
  “ (((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre))) ” &&
  “ ((Z.quot exponent 2) <= exponent_pre) ” &&
  “ ((0 : Int) <= (Z.quot exponent 2)) ” &&
  “ ((Z.rem (base * base) modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem (base * base) modulus_pre)) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_2_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  (EulerModularPowerProgress base_pre exponent_pre modulus_pre (Z.rem (base * base) modulus_pre) (Z.quot exponent 2) result)

noncomputable def modular_power_entail_wit_2_2_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((result * (Z.rem (base * base) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_2_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= (result * (Z.rem (base * base) modulus_pre)))

noncomputable def modular_power_entail_wit_2_2_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  (((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)) <= INT_MAX)

noncomputable def modular_power_entail_wit_2_2_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= ((Z.rem (base * base) modulus_pre) * (Z.rem (base * base) modulus_pre)))

noncomputable def modular_power_entail_wit_2_2_split_goal_6 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((Z.quot exponent 2) <= exponent_pre)

noncomputable def modular_power_entail_wit_2_2_split_goal_7 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= (Z.quot exponent 2))

noncomputable def modular_power_entail_wit_2_2_split_goal_8 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((Z.rem (base * base) modulus_pre) < modulus_pre)

noncomputable def modular_power_entail_wit_2_2_split_goal_9 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : ((Z.rem exponent 2) ≠ 1)) (PreH2 : (exponent > (0 : Int))) (PreH3 : ((0 : Int) <= base_pre)) (PreH4 : (base_pre < modulus_pre)) (PreH5 : ((0 : Int) <= exponent_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((0 : Int) <= base)) (PreH9 : (base < modulus_pre)) (PreH10 : ((0 : Int) <= exponent)) (PreH11 : (exponent <= exponent_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < modulus_pre)) (PreH14 : ((0 : Int) <= (base * base))) (PreH15 : ((base * base) <= INT_MAX)) (PreH16 : ((0 : Int) <= (result * base))) (PreH17 : ((result * base) <= INT_MAX)) (PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  ((0 : Int) <= (Z.rem (base * base) modulus_pre))

noncomputable def modular_power_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : (exponent <= (0 : Int))) (PreH2 : ((0 : Int) <= base_pre)) (PreH3 : (base_pre < modulus_pre)) (PreH4 : ((0 : Int) <= exponent_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= base)) (PreH8 : (base < modulus_pre)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent <= exponent_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (base * base))) (PreH14 : ((base * base) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * base))) (PreH16 : ((result * base) <= INT_MAX)) (PreH17 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= result) ” &&
  “ (result < modulus_pre) ” &&
  “ (ModularPower base_pre exponent_pre modulus_pre result) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : (exponent <= (0 : Int))) (PreH2 : ((0 : Int) <= base_pre)) (PreH3 : (base_pre < modulus_pre)) (PreH4 : ((0 : Int) <= exponent_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= base)) (PreH8 : (base < modulus_pre)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent <= exponent_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (base * base))) (PreH14 : ((base * base) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * base))) (PreH16 : ((result * base) <= INT_MAX)) (PreH17 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  TT && emp 
|--
  “ (ModularPower base_pre exponent_pre modulus_pre result) ”
  &&  emp
)

noncomputable def modular_power_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (exponent_pre : Int) (base_pre : Int) (result : Int) (exponent : Int) (base : Int) (PreH1 : (exponent <= (0 : Int))) (PreH2 : ((0 : Int) <= base_pre)) (PreH3 : (base_pre < modulus_pre)) (PreH4 : ((0 : Int) <= exponent_pre)) (PreH5 : (2 <= modulus_pre)) (PreH6 : (modulus_pre <= 46341)) (PreH7 : ((0 : Int) <= base)) (PreH8 : (base < modulus_pre)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent <= exponent_pre)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < modulus_pre)) (PreH13 : ((0 : Int) <= (base * base))) (PreH14 : ((base * base) <= INT_MAX)) (PreH15 : ((0 : Int) <= (result * base))) (PreH16 : ((result * base) <= INT_MAX)) (PreH17 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result)) ,
  (ModularPower base_pre exponent_pre modulus_pre result)

noncomputable def euler_theorem_inverse_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (retval : Int) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  ((( &( "exponent" ) )) # Int |->_)
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ ((retval - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval - 1)) ”

noncomputable def euler_theorem_inverse_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (retval : Int) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  ((( &( "exponent" ) )) # Int |->_)
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def euler_theorem_inverse_entail_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (value_pre : Int) (retval : Int) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ ((0 : Int) < value_pre) ” &&
  “ (value_pre < modulus_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((Zgcd (value_pre) (modulus_pre)) = 1) ” &&
  “ ((0 : Int) <= (retval - 1)) ” &&
  “ ((retval - 1) < modulus_pre) ” &&
  “ (EulerPhi modulus_pre ((retval - 1) + 1)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (value_pre : Int) (retval : Int) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (EulerPhi modulus_pre ((retval - 1) + 1)) ”
  &&  emp
)

noncomputable def euler_theorem_inverse_entail_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (retval : Int) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  (EulerPhi modulus_pre ((retval - 1) + 1))

noncomputable def euler_theorem_inverse_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (value_pre : Int) (exponent : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < modulus_pre)) (PreH3 : (ModularPower value_pre exponent modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent < modulus_pre)) (PreH11 : (EulerPhi modulus_pre (exponent + 1))) ,
  TT && emp 
|--
  “ ((0 : Int) <= retval) ” &&
  “ (retval < modulus_pre) ” &&
  “ (EulerTheoremInverse value_pre modulus_pre retval) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (value_pre : Int) (exponent : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < modulus_pre)) (PreH3 : (ModularPower value_pre exponent modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent < modulus_pre)) (PreH11 : (EulerPhi modulus_pre (exponent + 1))) ,
  TT && emp 
|--
  “ (EulerTheoremInverse value_pre modulus_pre retval) ”
  &&  emp
)

noncomputable def euler_theorem_inverse_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (exponent : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval < modulus_pre)) (PreH3 : (ModularPower value_pre exponent modulus_pre retval)) (PreH4 : ((0 : Int) < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) (PreH9 : ((0 : Int) <= exponent)) (PreH10 : (exponent < modulus_pre)) (PreH11 : (EulerPhi modulus_pre (exponent + 1))) ,
  (EulerTheoremInverse value_pre modulus_pre retval)

noncomputable def euler_theorem_inverse_partial_solve_wit_1_pure : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (PreH1 : ((0 : Int) < value_pre)) (PreH2 : (value_pre < modulus_pre)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  ((( &( "exponent" ) )) # Int |->_)
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ”

noncomputable def euler_theorem_inverse_partial_solve_wit_1_aux : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (PreH1 : ((0 : Int) < value_pre)) (PreH2 : (value_pre < modulus_pre)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) < value_pre) ” &&
  “ (value_pre < modulus_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((Zgcd (value_pre) (modulus_pre)) = 1) ”
  &&  emp

noncomputable def euler_theorem_inverse_partial_solve_wit_1 : Prop := euler_theorem_inverse_partial_solve_wit_1_pure -> euler_theorem_inverse_partial_solve_wit_1_aux

noncomputable def euler_theorem_inverse_partial_solve_wit_2_pure : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (exponent : Int) (PreH1 : ((0 : Int) < value_pre)) (PreH2 : (value_pre < modulus_pre)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : ((Zgcd (value_pre) (modulus_pre)) = 1)) (PreH6 : ((0 : Int) <= exponent)) (PreH7 : (exponent < modulus_pre)) (PreH8 : (EulerPhi modulus_pre (exponent + 1))) ,
  ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
|--
  “ ((0 : Int) <= value_pre) ” &&
  “ (value_pre < modulus_pre) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ”

noncomputable def euler_theorem_inverse_partial_solve_wit_2_aux : Prop :=
  forall (modulus_pre : Int) (value_pre : Int) (exponent : Int) (PreH1 : ((0 : Int) < value_pre)) (PreH2 : (value_pre < modulus_pre)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : ((Zgcd (value_pre) (modulus_pre)) = 1)) (PreH6 : ((0 : Int) <= exponent)) (PreH7 : (exponent < modulus_pre)) (PreH8 : (EulerPhi modulus_pre (exponent + 1))) ,
  TT && emp 
|--
  “ ((0 : Int) <= value_pre) ” &&
  “ (value_pre < modulus_pre) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((0 : Int) < value_pre) ” &&
  “ (value_pre < modulus_pre) ” &&
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 46341) ” &&
  “ ((Zgcd (value_pre) (modulus_pre)) = 1) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (exponent < modulus_pre) ” &&
  “ (EulerPhi modulus_pre (exponent + 1)) ”
  &&  emp

noncomputable def euler_theorem_inverse_partial_solve_wit_2 : Prop := euler_theorem_inverse_partial_solve_wit_2_pure -> euler_theorem_inverse_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_euler_phi_safety_wit_1 : euler_phi_safety_wit_1
  proof_of_euler_phi_safety_wit_2 : euler_phi_safety_wit_2
  proof_of_euler_phi_safety_wit_3 : euler_phi_safety_wit_3
  proof_of_euler_phi_safety_wit_4 : euler_phi_safety_wit_4
  proof_of_euler_phi_safety_wit_5 : euler_phi_safety_wit_5
  proof_of_euler_phi_safety_wit_6 : euler_phi_safety_wit_6
  proof_of_euler_phi_safety_wit_7 : euler_phi_safety_wit_7
  proof_of_euler_phi_safety_wit_8 : euler_phi_safety_wit_8
  proof_of_euler_phi_safety_wit_9 : euler_phi_safety_wit_9
  proof_of_euler_phi_safety_wit_10 : euler_phi_safety_wit_10
  proof_of_euler_phi_safety_wit_11 : euler_phi_safety_wit_11
  proof_of_euler_phi_safety_wit_12 : euler_phi_safety_wit_12
  proof_of_euler_phi_safety_wit_13 : euler_phi_safety_wit_13
  proof_of_euler_phi_safety_wit_14 : euler_phi_safety_wit_14
  proof_of_euler_phi_safety_wit_15 : euler_phi_safety_wit_15
  proof_of_euler_phi_safety_wit_16 : euler_phi_safety_wit_16
  proof_of_euler_phi_safety_wit_17 : euler_phi_safety_wit_17
  proof_of_euler_phi_safety_wit_18 : euler_phi_safety_wit_18
  proof_of_euler_phi_safety_wit_19 : euler_phi_safety_wit_19
  proof_of_euler_phi_safety_wit_20 : euler_phi_safety_wit_20
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
  proof_of_euler_theorem_inverse_safety_wit_1 : euler_theorem_inverse_safety_wit_1
  proof_of_euler_theorem_inverse_safety_wit_2 : euler_theorem_inverse_safety_wit_2
  proof_of_euler_theorem_inverse_partial_solve_wit_1_pure : euler_theorem_inverse_partial_solve_wit_1_pure
  proof_of_euler_theorem_inverse_partial_solve_wit_1 : euler_theorem_inverse_partial_solve_wit_1
  proof_of_euler_theorem_inverse_partial_solve_wit_2_pure : euler_theorem_inverse_partial_solve_wit_2_pure
  proof_of_euler_theorem_inverse_partial_solve_wit_2 : euler_theorem_inverse_partial_solve_wit_2
  proof_of_euler_phi_entail_wit_1 : euler_phi_entail_wit_1
  proof_of_euler_phi_entail_wit_2 : euler_phi_entail_wit_2
  proof_of_euler_phi_entail_wit_3 : euler_phi_entail_wit_3
  proof_of_euler_phi_entail_wit_4 : euler_phi_entail_wit_4
  proof_of_euler_phi_entail_wit_5_1 : euler_phi_entail_wit_5_1
  proof_of_euler_phi_entail_wit_5_2 : euler_phi_entail_wit_5_2
  proof_of_euler_phi_entail_wit_6 : euler_phi_entail_wit_6
  proof_of_euler_phi_return_wit_1 : euler_phi_return_wit_1
  proof_of_euler_phi_return_wit_2 : euler_phi_return_wit_2
  proof_of_euler_phi_return_wit_3 : euler_phi_return_wit_3
  proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1
  proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1
  proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2
  proof_of_modular_power_return_wit_1 : modular_power_return_wit_1
  proof_of_euler_theorem_inverse_entail_wit_1 : euler_theorem_inverse_entail_wit_1
  proof_of_euler_theorem_inverse_return_wit_1 : euler_theorem_inverse_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_goal
