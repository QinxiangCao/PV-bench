import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance chinese_remainder_theorem_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def chinese_remainder_theorem_safety_wit_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  ((( &( "product" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def chinese_remainder_theorem_safety_wit_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "product" ) )) # Int |-> (1))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_3 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((product * (Znth i moduli_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (product * (Znth i moduli_l (0 : Int)))) ”
) \/
(
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((product * (Znth i moduli_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (product * (Znth i moduli_l (0 : Int)))) ”
)

noncomputable def chinese_remainder_theorem_safety_wit_3_split_goal_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((product * (Znth i moduli_l (0 : Int))) <= INT_MAX) ”

noncomputable def chinese_remainder_theorem_safety_wit_3_split_goal_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((INT_MIN) <= (product * (Znth i moduli_l (0 : Int)))) ”

noncomputable def chinese_remainder_theorem_safety_wit_4 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "product" ) )) # Int |-> ((product * (Znth i moduli_l (0 : Int)))))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def chinese_remainder_theorem_safety_wit_5 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_6 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_7 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((product ≠ (INT_MIN)) ∨ ((Znth i moduli_l (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth i moduli_l (0 : Int)) ≠ (0 : Int)) ”
) \/
(
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((product ≠ (INT_MIN)) ∨ ((Znth i moduli_l (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth i moduli_l (0 : Int)) ≠ (0 : Int)) ”
)

noncomputable def chinese_remainder_theorem_safety_wit_7_split_goal_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((product ≠ (INT_MIN)) ∨ ((Znth i moduli_l (0 : Int)) ≠ (-1))) ”

noncomputable def chinese_remainder_theorem_safety_wit_7_split_goal_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((Znth i moduli_l (0 : Int)) ≠ (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_8 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((( &( "term" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ (((x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) ≠ (INT_MIN)) ∨ (product ≠ (-1))) ” &&
  “ (product ≠ (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_9 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((( &( "term" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int))))) ”
) \/
(
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((( &( "term" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int))))) ”
)

noncomputable def chinese_remainder_theorem_safety_wit_9_split_goal_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((( &( "term" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) <= INT_MAX) ”

noncomputable def chinese_remainder_theorem_safety_wit_9_split_goal_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((( &( "term" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((INT_MIN) <= (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int))))) ”

noncomputable def chinese_remainder_theorem_safety_wit_10 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) ≠ (INT_MIN)) ∨ (product ≠ (-1))) ” &&
  “ (product ≠ (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_11 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int)))) ”
) \/
(
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int)))) ”
)

noncomputable def chinese_remainder_theorem_safety_wit_11_split_goal_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) <= INT_MAX) ”

noncomputable def chinese_remainder_theorem_safety_wit_11_split_goal_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((INT_MIN) <= ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int)))) ”

noncomputable def chinese_remainder_theorem_safety_wit_12 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_13 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) ”

noncomputable def chinese_remainder_theorem_safety_wit_14 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> (((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) ≠ (INT_MIN)) ∨ (product ≠ (-1))) ” &&
  “ (product ≠ (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_15 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> (((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product))) ”

noncomputable def chinese_remainder_theorem_safety_wit_16 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) ≠ (INT_MIN)) ∨ (product ≠ (-1))) ” &&
  “ (product ≠ (0 : Int)) ”

noncomputable def chinese_remainder_theorem_safety_wit_17 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product))) ”
) \/
(
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product))) ”
)

noncomputable def chinese_remainder_theorem_safety_wit_17_split_goal_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) <= INT_MAX) ”

noncomputable def chinese_remainder_theorem_safety_wit_17_split_goal_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** ((( &( "term" ) )) # Int |-> ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)))
  ** ((( &( "coefficient" ) )) # Int |-> (x_callee_v))
  ** ((( &( "unused" ) )) # Int |-> (y_callee_v))
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((INT_MIN) <= (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product))) ”

noncomputable def chinese_remainder_theorem_safety_wit_18 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def chinese_remainder_theorem_safety_wit_19 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> ((Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def chinese_remainder_theorem_entail_wit_1 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (1 = (CRTProduct ((sublist ((0 : Int)) ((0 : Int)) (moduli_l))))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (CRTProduct (moduli_l))) ” &&
  “ ((CRTProduct (moduli_l)) <= 46340) ”
  &&  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
) \/
(
forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  TT && emp 
|--
  “ ((CRTProduct (moduli_l)) <= 46340) ” &&
  “ (1 <= (CRTProduct (moduli_l))) ” &&
  “ (1 = (CRTProduct ((sublist ((0 : Int)) ((0 : Int)) (moduli_l))))) ” &&
  “ ((0 : Int) <= n_pre) ”
  &&  emp
)

noncomputable def chinese_remainder_theorem_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  ((CRTProduct (moduli_l)) <= 46340)

noncomputable def chinese_remainder_theorem_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  (1 <= (CRTProduct (moduli_l)))

noncomputable def chinese_remainder_theorem_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  (1 = (CRTProduct ((sublist ((0 : Int)) ((0 : Int)) (moduli_l)))))

noncomputable def chinese_remainder_theorem_entail_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : (CRTInputValid remainders_l moduli_l)) (PreH3 : (CRTMachineSafe remainders_l moduli_l)) ,
  ((0 : Int) <= n_pre)

noncomputable def chinese_remainder_theorem_entail_wit_2 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((product * (Znth i moduli_l (0 : Int))) = (CRTProduct ((sublist ((0 : Int)) ((i + 1)) (moduli_l))))) ” &&
  “ (1 <= (product * (Znth i moduli_l (0 : Int)))) ” &&
  “ ((product * (Znth i moduli_l (0 : Int))) <= (CRTProduct (moduli_l))) ” &&
  “ ((CRTProduct (moduli_l)) <= 46340) ”
  &&  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
) \/
(
forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  TT && emp 
|--
  “ ((product * (Znth i moduli_l (0 : Int))) <= (CRTProduct (moduli_l))) ” &&
  “ (1 <= (product * (Znth i moduli_l (0 : Int)))) ” &&
  “ ((product * (Znth i moduli_l (0 : Int))) = (CRTProduct ((sublist ((0 : Int)) ((i + 1)) (moduli_l))))) ”
  &&  emp
)

noncomputable def chinese_remainder_theorem_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  ((product * (Znth i moduli_l (0 : Int))) <= (CRTProduct (moduli_l)))

noncomputable def chinese_remainder_theorem_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (1 <= (product * (Znth i moduli_l (0 : Int))))

noncomputable def chinese_remainder_theorem_entail_wit_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  ((product * (Znth i moduli_l (0 : Int))) = (CRTProduct ((sublist ((0 : Int)) ((i + 1)) (moduli_l)))))

noncomputable def chinese_remainder_theorem_entail_wit_3 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ (product = (CRTProduct (moduli_l))) ” &&
  “ (1 <= product) ” &&
  “ (product <= 46340) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < product) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l (0 : Int) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Z.rem (0 : Int) (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ”
  &&  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
) \/
(
forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Z.rem (0 : Int) (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l (0 : Int) (0 : Int)) ” &&
  “ (product = (CRTProduct (moduli_l))) ”
  &&  emp
)

noncomputable def chinese_remainder_theorem_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Z.rem (0 : Int) (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))

noncomputable def chinese_remainder_theorem_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (CRTProcessedCongruences remainders_l moduli_l (0 : Int) (0 : Int))

noncomputable def chinese_remainder_theorem_entail_wit_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (product = (CRTProduct (moduli_l)))

noncomputable def chinese_remainder_theorem_entail_wit_4_1 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ (product = (CRTProduct (moduli_l))) ” &&
  “ (1 <= product) ” &&
  “ (product <= 46340) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product)) ” &&
  “ ((Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product) < product) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l (i + 1) (Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product)) ” &&
  “ forall (k : Int) , ((((i + 1) <= k) ∧ (k < n_pre)) -> ((Z.rem (Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product) (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ”
  &&  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
) \/
(
forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  TT && emp 
|--
  “ (CRTProcessedCongruences remainders_l moduli_l (i + 1) (Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product)) ” &&
  “ ((Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product) < product) ” &&
  “ ((0 : Int) <= (Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product)) ”
  &&  emp
)

noncomputable def chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (CRTProcessedCongruences remainders_l moduli_l (i + 1) (Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product))

noncomputable def chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product) < product)

noncomputable def chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) < (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((0 : Int) <= (Z.rem (result + ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) + product)) product))

noncomputable def chinese_remainder_theorem_entail_wit_4_2 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ (product = (CRTProduct (moduli_l))) ” &&
  “ (1 <= product) ” &&
  “ (product <= 46340) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product)) ” &&
  “ ((Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product) < product) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l (i + 1) (Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product)) ” &&
  “ forall (k : Int) , ((((i + 1) <= k) ∧ (k < n_pre)) -> ((Z.rem (Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product) (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ”
  &&  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
) \/
(
forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  TT && emp 
|--
  “ (CRTProcessedCongruences remainders_l moduli_l (i + 1) (Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product)) ” &&
  “ ((Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product) < product) ” &&
  “ ((0 : Int) <= (Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product)) ”
  &&  emp
)

noncomputable def chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (CRTProcessedCongruences remainders_l moduli_l (i + 1) (Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product))

noncomputable def chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product) < product)

noncomputable def chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product) >= (0 : Int))) (PreH2 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : (CRTInputValid remainders_l moduli_l)) (PreH7 : (CRTMachineSafe remainders_l moduli_l)) (PreH8 : (product = (CRTProduct (moduli_l)))) (PreH9 : (1 <= product)) (PreH10 : (product <= 46340)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= result)) (PreH14 : (result < product)) (PreH15 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH16 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  ((0 : Int) <= (Z.rem (result + (Z.rem ((Z.rem (x_callee_v * (Z.quot product (Znth i moduli_l (0 : Int)))) product) * (Znth i remainders_l (0 : Int))) product)) product))

noncomputable def chinese_remainder_theorem_return_wit_1 : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (CanonicalCRTSolution remainders_l moduli_l result) ”
  &&  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
) \/
(
forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  TT && emp 
|--
  “ (CanonicalCRTSolution remainders_l moduli_l result) ”
  &&  emp
)

noncomputable def chinese_remainder_theorem_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (CanonicalCRTSolution remainders_l moduli_l result)

noncomputable def chinese_remainder_theorem_partial_solve_wit_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (product : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l)))))) (PreH8 : (1 <= product)) (PreH9 : (product <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (product = (CRTProduct ((sublist ((0 : Int)) (i) (moduli_l))))) ” &&
  “ (1 <= product) ” &&
  “ (product <= (CRTProduct (moduli_l))) ” &&
  “ ((CRTProduct (moduli_l)) <= 46340) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i moduli_l (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)

noncomputable def chinese_remainder_theorem_partial_solve_wit_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full remainders_pre n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ (product = (CRTProduct (moduli_l))) ” &&
  “ (1 <= product) ” &&
  “ (product <= 46340) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < product) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l i result) ” &&
  “ forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i moduli_l (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)

noncomputable def chinese_remainder_theorem_partial_solve_wit_3 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ (product = (CRTProduct (moduli_l))) ” &&
  “ (1 <= product) ” &&
  “ (product <= 46340) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < product) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l i result) ” &&
  “ forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i moduli_l (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)

noncomputable def chinese_remainder_theorem_partial_solve_wit_4_pure : Prop :=
  (
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "unused" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |->_)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((Znth i moduli_l (0 : Int)) <= INT_MAX) ” &&
  “ (INT_MIN < (Znth i moduli_l (0 : Int))) ” &&
  “ ((Z.quot product (Znth i moduli_l (0 : Int))) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot product (Znth i moduli_l (0 : Int)))) ”
) \/
(
forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.quot product (Znth i moduli_l (0 : Int))) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.quot product (Znth i moduli_l (0 : Int))) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : (CRTInputValid remainders_l moduli_l)) (PreH14 : (CRTMachineSafe remainders_l moduli_l)) (PreH15 : (product = (CRTProduct (moduli_l)))) (PreH16 : (1 <= product)) (PreH17 : (product <= 46340)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= result)) (PreH21 : (result < product)) (PreH22 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH23 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "unused" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |->_)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ (INT_MIN < (Z.quot product (Znth i moduli_l (0 : Int)))) ” &&
  “ (INT_MIN < (Znth i moduli_l (0 : Int))) ” &&
  “ ((Znth i moduli_l (0 : Int)) <= INT_MAX) ”
)

noncomputable def chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.quot product (Znth i moduli_l (0 : Int))) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.quot product (Znth i moduli_l (0 : Int))) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : (CRTInputValid remainders_l moduli_l)) (PreH14 : (CRTMachineSafe remainders_l moduli_l)) (PreH15 : (product = (CRTProduct (moduli_l)))) (PreH16 : (1 <= product)) (PreH17 : (product <= 46340)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= result)) (PreH21 : (result < product)) (PreH22 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH23 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "unused" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |->_)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ (INT_MIN < (Z.quot product (Znth i moduli_l (0 : Int)))) ”

noncomputable def chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.quot product (Znth i moduli_l (0 : Int))) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.quot product (Znth i moduli_l (0 : Int))) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : (CRTInputValid remainders_l moduli_l)) (PreH14 : (CRTMachineSafe remainders_l moduli_l)) (PreH15 : (product = (CRTProduct (moduli_l)))) (PreH16 : (1 <= product)) (PreH17 : (product <= 46340)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= result)) (PreH21 : (result < product)) (PreH22 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH23 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "unused" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |->_)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ (INT_MIN < (Znth i moduli_l (0 : Int))) ”

noncomputable def chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Z.quot product (Znth i moduli_l (0 : Int))) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((Z.quot product (Znth i moduli_l (0 : Int))) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : (CRTInputValid remainders_l moduli_l)) (PreH14 : (CRTMachineSafe remainders_l moduli_l)) (PreH15 : (product = (CRTProduct (moduli_l)))) (PreH16 : (1 <= product)) (PreH17 : (product <= 46340)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= result)) (PreH21 : (result < product)) (PreH22 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH23 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** ((( &( "unused" ) )) # Int |->_)
  ** ((( &( "coefficient" ) )) # Int |->_)
  ** ((( &( "partial_product" ) )) # Int |-> ((Z.quot product (Znth i moduli_l (0 : Int)))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "remainders" ) )) # Ptr |-> (remainders_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "product" ) )) # Int |-> (product))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result" ) )) # Int |-> (result))
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((Znth i moduli_l (0 : Int)) <= INT_MAX) ”

noncomputable def chinese_remainder_theorem_partial_solve_wit_4_aux : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : (CRTInputValid remainders_l moduli_l)) (PreH4 : (CRTMachineSafe remainders_l moduli_l)) (PreH5 : (product = (CRTProduct (moduli_l)))) (PreH6 : (1 <= product)) (PreH7 : (product <= 46340)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < product)) (PreH12 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH13 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ ((Znth i moduli_l (0 : Int)) <= INT_MAX) ” &&
  “ (INT_MIN < (Znth i moduli_l (0 : Int))) ” &&
  “ ((Z.quot product (Znth i moduli_l (0 : Int))) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot product (Znth i moduli_l (0 : Int)))) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ (product = (CRTProduct (moduli_l))) ” &&
  “ (1 <= product) ” &&
  “ (product <= 46340) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < product) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l i result) ” &&
  “ forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ”
  &&  (intArray.full moduli_pre n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)

noncomputable def chinese_remainder_theorem_partial_solve_wit_4 : Prop := chinese_remainder_theorem_partial_solve_wit_4_pure -> chinese_remainder_theorem_partial_solve_wit_4_aux

noncomputable def chinese_remainder_theorem_partial_solve_wit_5 : Prop :=
  forall (moduli_pre : Int) (remainders_pre : Int) (n_pre : Int) (moduli_l : (List Int)) (remainders_l : (List Int)) (result : Int) (i : Int) (product : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH2 : ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int)))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : (CRTInputValid remainders_l moduli_l)) (PreH6 : (CRTMachineSafe remainders_l moduli_l)) (PreH7 : (product = (CRTProduct (moduli_l)))) (PreH8 : (1 <= product)) (PreH9 : (product <= 46340)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= result)) (PreH13 : (result < product)) (PreH14 : (CRTProcessedCongruences remainders_l moduli_l i result)) (PreH15 : forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int)))) ,
  (intArray.full moduli_pre n_pre moduli_l)
  ** (intArray.full remainders_pre n_pre remainders_l)
|--
  “ (retval = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int))))) ” &&
  “ ((((Z.quot product (Znth i moduli_l (0 : Int))) * x_callee_v) + ((Znth i moduli_l (0 : Int)) * y_callee_v)) = (Zgcd ((Z.quot product (Znth i moduli_l (0 : Int)))) ((Znth i moduli_l (0 : Int))))) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (moduli_l))) ” &&
  “ (CRTInputValid remainders_l moduli_l) ” &&
  “ (CRTMachineSafe remainders_l moduli_l) ” &&
  “ (product = (CRTProduct (moduli_l))) ” &&
  “ (1 <= product) ” &&
  “ (product <= 46340) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < product) ” &&
  “ (CRTProcessedCongruences remainders_l moduli_l i result) ” &&
  “ forall (k : Int) , (((i <= k) ∧ (k < n_pre)) -> ((Z.rem result (Znth (k) (moduli_l) ((0 : Int)))) = (0 : Int))) ”
  &&  (((remainders_pre + (i * sizeof(INT)))) # Int |-> ((Znth i remainders_l (0 : Int))))
  ** (intArray.missing_i remainders_pre i (0 : Int) n_pre remainders_l)
  ** (intArray.full moduli_pre n_pre moduli_l)


structure VC_Correct : Type where
  proof_of_chinese_remainder_theorem_safety_wit_1 : chinese_remainder_theorem_safety_wit_1
  proof_of_chinese_remainder_theorem_safety_wit_2 : chinese_remainder_theorem_safety_wit_2
  proof_of_chinese_remainder_theorem_safety_wit_4 : chinese_remainder_theorem_safety_wit_4
  proof_of_chinese_remainder_theorem_safety_wit_5 : chinese_remainder_theorem_safety_wit_5
  proof_of_chinese_remainder_theorem_safety_wit_6 : chinese_remainder_theorem_safety_wit_6
  proof_of_chinese_remainder_theorem_safety_wit_8 : chinese_remainder_theorem_safety_wit_8
  proof_of_chinese_remainder_theorem_safety_wit_10 : chinese_remainder_theorem_safety_wit_10
  proof_of_chinese_remainder_theorem_safety_wit_12 : chinese_remainder_theorem_safety_wit_12
  proof_of_chinese_remainder_theorem_safety_wit_13 : chinese_remainder_theorem_safety_wit_13
  proof_of_chinese_remainder_theorem_safety_wit_14 : chinese_remainder_theorem_safety_wit_14
  proof_of_chinese_remainder_theorem_safety_wit_15 : chinese_remainder_theorem_safety_wit_15
  proof_of_chinese_remainder_theorem_safety_wit_16 : chinese_remainder_theorem_safety_wit_16
  proof_of_chinese_remainder_theorem_safety_wit_18 : chinese_remainder_theorem_safety_wit_18
  proof_of_chinese_remainder_theorem_safety_wit_19 : chinese_remainder_theorem_safety_wit_19
  proof_of_chinese_remainder_theorem_partial_solve_wit_1 : chinese_remainder_theorem_partial_solve_wit_1
  proof_of_chinese_remainder_theorem_partial_solve_wit_2 : chinese_remainder_theorem_partial_solve_wit_2
  proof_of_chinese_remainder_theorem_partial_solve_wit_3 : chinese_remainder_theorem_partial_solve_wit_3
  proof_of_chinese_remainder_theorem_partial_solve_wit_4 : chinese_remainder_theorem_partial_solve_wit_4
  proof_of_chinese_remainder_theorem_partial_solve_wit_5 : chinese_remainder_theorem_partial_solve_wit_5
  proof_of_chinese_remainder_theorem_safety_wit_3 : chinese_remainder_theorem_safety_wit_3
  proof_of_chinese_remainder_theorem_safety_wit_7 : chinese_remainder_theorem_safety_wit_7
  proof_of_chinese_remainder_theorem_safety_wit_9 : chinese_remainder_theorem_safety_wit_9
  proof_of_chinese_remainder_theorem_safety_wit_11 : chinese_remainder_theorem_safety_wit_11
  proof_of_chinese_remainder_theorem_safety_wit_17 : chinese_remainder_theorem_safety_wit_17
  proof_of_chinese_remainder_theorem_entail_wit_1 : chinese_remainder_theorem_entail_wit_1
  proof_of_chinese_remainder_theorem_entail_wit_2 : chinese_remainder_theorem_entail_wit_2
  proof_of_chinese_remainder_theorem_entail_wit_3 : chinese_remainder_theorem_entail_wit_3
  proof_of_chinese_remainder_theorem_entail_wit_4_1 : chinese_remainder_theorem_entail_wit_4_1
  proof_of_chinese_remainder_theorem_entail_wit_4_2 : chinese_remainder_theorem_entail_wit_4_2
  proof_of_chinese_remainder_theorem_return_wit_1 : chinese_remainder_theorem_return_wit_1
  proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure : chinese_remainder_theorem_partial_solve_wit_4_pure

end SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_goal
