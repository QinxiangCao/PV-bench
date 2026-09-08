import SimpleC.SL.SeparationLogic

import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.modular_inverse.lean.groundtruth.modular_inverse_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance modular_inverse_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def modular_inverse_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH2 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (1 < modulus_pre)) (PreH4 : ((0 : Int) < a_pre)) (PreH5 : (a_pre < modulus_pre)) (PreH6 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ ((x_callee_v ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_inverse_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH2 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (1 < modulus_pre)) (PreH4 : ((0 : Int) < a_pre)) (PreH5 : (a_pre < modulus_pre)) (PreH6 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int |-> ((Z.rem x_callee_v modulus_pre)))
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_inverse_safety_wit_3 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int |-> ((Z.rem x_callee_v modulus_pre)))
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (((Z.rem x_callee_v modulus_pre) + modulus_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ”

noncomputable def modular_inverse_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  EX k : Int,
  “ ((0 : Int) <= ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ” &&
  “ (((Z.rem x_callee_v modulus_pre) + modulus_pre) < modulus_pre) ” &&
  “ (((a_pre * ((Z.rem x_callee_v modulus_pre) + modulus_pre)) + (modulus_pre * k)) = 1) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  EX k : Int,
  “ ((0 : Int) <= ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ” &&
  “ (((Z.rem x_callee_v modulus_pre) + modulus_pre) < modulus_pre) ” &&
  “ (((a_pre * ((Z.rem x_callee_v modulus_pre) + modulus_pre)) + (modulus_pre * k)) = 1) ”
  &&  emp
)

noncomputable def modular_inverse_return_wit_2 : Prop :=
  (
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) >= (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  EX k : Int,
  “ ((0 : Int) <= (Z.rem x_callee_v modulus_pre)) ” &&
  “ ((Z.rem x_callee_v modulus_pre) < modulus_pre) ” &&
  “ (((a_pre * (Z.rem x_callee_v modulus_pre)) + (modulus_pre * k)) = 1) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) >= (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  EX k : Int,
  “ ((0 : Int) <= (Z.rem x_callee_v modulus_pre)) ” &&
  “ ((Z.rem x_callee_v modulus_pre) < modulus_pre) ” &&
  “ (((a_pre * (Z.rem x_callee_v modulus_pre)) + (modulus_pre * k)) = 1) ”
  &&  emp
)

noncomputable def modular_inverse_partial_solve_wit_1_pure : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (PreH1 : (1 < modulus_pre)) (PreH2 : ((0 : Int) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "g" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (INT_MIN < modulus_pre) ” &&
  “ (modulus_pre <= INT_MAX) ” &&
  “ (a_pre <= INT_MAX) ”

noncomputable def modular_inverse_partial_solve_wit_1_aux : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (PreH1 : (1 < modulus_pre)) (PreH2 : ((0 : Int) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (INT_MIN < a_pre) ” &&
  “ (INT_MIN < modulus_pre) ” &&
  “ (modulus_pre <= INT_MAX) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (1 < modulus_pre) ” &&
  “ ((0 : Int) < a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ ((Zgcd (a_pre) (modulus_pre)) = 1) ”
  &&  emp

noncomputable def modular_inverse_partial_solve_wit_1 : Prop := modular_inverse_partial_solve_wit_1_pure -> modular_inverse_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_modular_inverse_safety_wit_1 : modular_inverse_safety_wit_1
  proof_of_modular_inverse_safety_wit_2 : modular_inverse_safety_wit_2
  proof_of_modular_inverse_safety_wit_3 : modular_inverse_safety_wit_3
  proof_of_modular_inverse_partial_solve_wit_1_pure : modular_inverse_partial_solve_wit_1_pure
  proof_of_modular_inverse_partial_solve_wit_1 : modular_inverse_partial_solve_wit_1
  proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1
  proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2

end Algorithms.modular_inverse.lean.groundtruth.modular_inverse_goal
