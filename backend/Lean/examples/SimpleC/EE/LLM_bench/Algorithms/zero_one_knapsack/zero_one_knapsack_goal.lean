import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib
open SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance zero_one_knapsack_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def zeroOneKnapsack_safety_wit_1 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre)) ,
  ((( &( "width" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.undef_full dp_pre ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((capacity_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (capacity_pre + 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_2 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre)) ,
  ((( &( "width" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.undef_full dp_pre ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def zeroOneKnapsack_safety_wit_3 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "width" ) )) # Int |-> ((capacity_pre + 1)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.undef_full dp_pre ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def zeroOneKnapsack_safety_wit_4 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (i : Int) (width : Int) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l i)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) (i * width) dp_l)
  ** (intArray.undef_seg dp_pre (i * width) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def zeroOneKnapsack_safety_wit_5 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (capacity_pre + 1))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "idx" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * width) + j)) ”

noncomputable def zeroOneKnapsack_safety_wit_6 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (capacity_pre + 1))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "idx" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((i * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * width)) ”

noncomputable def zeroOneKnapsack_safety_wit_7 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= ((i * width) + j))) (PreH2 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (width <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (width >= INT_MIN)) (PreH11 : (capacity_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1))) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : ((0 : Int) <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i <= n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= (capacity_pre + 1))) (PreH23 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def zeroOneKnapsack_safety_wit_8 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (i = (0 : Int))) (PreH2 : ((0 : Int) <= ((i * width) + j))) (PreH3 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1))) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : ((0 : Int) <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (capacity_pre + 1))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def zeroOneKnapsack_safety_wit_9 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (i ≠ (0 : Int))) (PreH2 : ((0 : Int) <= ((i * width) + j))) (PreH3 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1))) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : ((0 : Int) <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (capacity_pre + 1))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def zeroOneKnapsack_safety_wit_10 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def zeroOneKnapsack_safety_wit_11 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "item" ) )) # Int |->_)
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_12 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "item" ) )) # Int |->_)
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def zeroOneKnapsack_safety_wit_13 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH2 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH3 : ((i - 1) <= INT_MAX)) (PreH4 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH6 : ((i - 1) >= INT_MIN)) (PreH7 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH8 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH9 : ((0 : Int) <= (i - 1))) (PreH10 : ((i - 1) < n_pre)) (PreH11 : (((i * width) + j) <= INT_MAX)) (PreH12 : (((i * width) + j) >= INT_MIN)) (PreH13 : (j ≠ (0 : Int))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : ((0 : Int) <= ((i * width) + j))) (PreH16 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : ((0 : Int) <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i <= n_pre)) (PreH35 : ((0 : Int) <= j)) (PreH36 : (j <= (capacity_pre + 1))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "without" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((((i - 1) * width) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i - 1) * width) + j)) ”

noncomputable def zeroOneKnapsack_safety_wit_14 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH2 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH3 : ((i - 1) <= INT_MAX)) (PreH4 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH6 : ((i - 1) >= INT_MIN)) (PreH7 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH8 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH9 : ((0 : Int) <= (i - 1))) (PreH10 : ((i - 1) < n_pre)) (PreH11 : (((i * width) + j) <= INT_MAX)) (PreH12 : (((i * width) + j) >= INT_MIN)) (PreH13 : (j ≠ (0 : Int))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : ((0 : Int) <= ((i * width) + j))) (PreH16 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : ((0 : Int) <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i <= n_pre)) (PreH35 : ((0 : Int) <= j)) (PreH36 : (j <= (capacity_pre + 1))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "without" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((i - 1) * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i - 1) * width)) ”

noncomputable def zeroOneKnapsack_safety_wit_15 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH2 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH3 : ((i - 1) <= INT_MAX)) (PreH4 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH6 : ((i - 1) >= INT_MIN)) (PreH7 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH8 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH9 : ((0 : Int) <= (i - 1))) (PreH10 : ((i - 1) < n_pre)) (PreH11 : (((i * width) + j) <= INT_MAX)) (PreH12 : (((i * width) + j) >= INT_MIN)) (PreH13 : (j ≠ (0 : Int))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : ((0 : Int) <= ((i * width) + j))) (PreH16 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : ((0 : Int) <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i <= n_pre)) (PreH35 : ((0 : Int) <= j)) (PreH36 : (j <= (capacity_pre + 1))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "without" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_16 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH2 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH3 : ((i - 1) <= INT_MAX)) (PreH4 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH6 : ((i - 1) >= INT_MIN)) (PreH7 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH8 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH9 : ((0 : Int) <= (i - 1))) (PreH10 : ((i - 1) < n_pre)) (PreH11 : (((i * width) + j) <= INT_MAX)) (PreH12 : (((i * width) + j) >= INT_MIN)) (PreH13 : (j ≠ (0 : Int))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : ((0 : Int) <= ((i * width) + j))) (PreH16 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : ((0 : Int) <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i <= n_pre)) (PreH35 : ((0 : Int) <= j)) (PreH36 : (j <= (capacity_pre + 1))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "without" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def zeroOneKnapsack_safety_wit_17 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "prev" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int))))) ”

noncomputable def zeroOneKnapsack_safety_wit_18 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "prev" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((j - (Znth (i - 1) weights_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - (Znth (i - 1) weights_l (0 : Int)))) ”

noncomputable def zeroOneKnapsack_safety_wit_19 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "prev" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((i - 1) * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i - 1) * width)) ”

noncomputable def zeroOneKnapsack_safety_wit_20 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "prev" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_21 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "prev" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def zeroOneKnapsack_safety_wit_22 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "with_val" ) )) # Int |->_)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "prev" ) )) # Int |-> ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int)))) ”
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "with_val" ) )) # Int |->_)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "prev" ) )) # Int |-> ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int)))) ”
)

noncomputable def zeroOneKnapsack_safety_wit_22_split_goal_1 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "with_val" ) )) # Int |->_)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "prev" ) )) # Int |-> ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= INT_MAX) ”

noncomputable def zeroOneKnapsack_safety_wit_22_split_goal_2 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "with_val" ) )) # Int |->_)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "prev" ) )) # Int |-> ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((INT_MIN) <= ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int)))) ”

noncomputable def zeroOneKnapsack_safety_wit_23 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (i = (0 : Int))) (PreH2 : ((0 : Int) <= ((i * width) + j))) (PreH3 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1))) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : ((0 : Int) <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (capacity_pre + 1))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_24 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_25 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) > (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l ++ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_26 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l ++ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_27 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((Znth (i - 1) weights_l (0 : Int)) > j)) (PreH2 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH3 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH4 : ((i - 1) <= INT_MAX)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH6 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH7 : ((i - 1) >= INT_MIN)) (PreH8 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH9 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : (((i * width) + j) <= INT_MAX)) (PreH13 : (((i * width) + j) >= INT_MIN)) (PreH14 : (j ≠ (0 : Int))) (PreH15 : (i ≠ (0 : Int))) (PreH16 : ((0 : Int) <= ((i * width) + j))) (PreH17 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1))) (PreH30 : ((0 : Int) <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : ((0 : Int) <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : ((0 : Int) <= i)) (PreH35 : (i <= n_pre)) (PreH36 : ((0 : Int) <= j)) (PreH37 : (j <= (capacity_pre + 1))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l ++ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_28 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (capacity_pre + 1))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def zeroOneKnapsack_safety_wit_29 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ (((n_pre * width) + capacity_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n_pre * width) + capacity_pre)) ”
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ (((n_pre * width) + capacity_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n_pre * width) + capacity_pre)) ”
)

noncomputable def zeroOneKnapsack_safety_wit_29_split_goal_1 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ (((n_pre * width) + capacity_pre) <= INT_MAX) ”

noncomputable def zeroOneKnapsack_safety_wit_29_split_goal_2 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ ((INT_MIN) <= ((n_pre * width) + capacity_pre)) ”

noncomputable def zeroOneKnapsack_safety_wit_30 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ ((n_pre * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * width)) ”
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ ((n_pre * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * width)) ”
)

noncomputable def zeroOneKnapsack_safety_wit_30_split_goal_1 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ ((n_pre * width) <= INT_MAX) ”

noncomputable def zeroOneKnapsack_safety_wit_30_split_goal_2 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ ((INT_MIN) <= (n_pre * width)) ”

noncomputable def zeroOneKnapsack_entail_wit_1 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.undef_full dp_pre ((n_pre + 1) * (capacity_pre + 1)))
|--
  EX dp_l : (List Int),
  “ ((capacity_pre + 1) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre (capacity_pre + 1) dp_l (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((0 : Int) * (capacity_pre + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((0 : Int) * (capacity_pre + 1)) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre)) ,
  (intArray.undef_full dp_pre ((n_pre + 1) * (capacity_pre + 1)))
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre (capacity_pre + 1) dp_l (0 : Int)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((0 : Int) * (capacity_pre + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((0 : Int) * (capacity_pre + 1)) ((n_pre + 1) * (capacity_pre + 1)))
)

noncomputable def zeroOneKnapsack_entail_wit_2 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (width : Int) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) (i * width) dp_l_2)
  ** (intArray.undef_seg dp_pre (i * width) ((n_pre + 1) * (capacity_pre + 1)))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + (0 : Int)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + (0 : Int)) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (width : Int) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i)) ,
  (intArray.seg dp_pre (0 : Int) (i * width) dp_l_2)
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (0 : Int)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * width) + (0 : Int)) dp_l)
)

noncomputable def zeroOneKnapsack_entail_wit_3 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (capacity_pre + 1))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (width <= INT_MAX)) (PreH4 : (capacity_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((i * width) + j) <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (width >= INT_MIN)) (PreH10 : (capacity_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (((i * width) + j) >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1))) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : ((0 : Int) <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i <= n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= (capacity_pre + 1))) (PreH23 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  TT && emp 
|--
  “ (((i * (capacity_pre + 1)) + j) < ((n_pre + 1) * (capacity_pre + 1))) ”
  &&  emp
)

noncomputable def zeroOneKnapsack_entail_wit_3_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (width <= INT_MAX)) (PreH4 : (capacity_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((i * width) + j) <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (width >= INT_MIN)) (PreH10 : (capacity_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (((i * width) + j) >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1))) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : ((0 : Int) <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i <= n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= (capacity_pre + 1))) (PreH23 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (((i * (capacity_pre + 1)) + j) < ((n_pre + 1) * (capacity_pre + 1)))

noncomputable def zeroOneKnapsack_entail_wit_4 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))

noncomputable def zeroOneKnapsack_entail_wit_5 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : (((i * width) + j) <= INT_MAX)) (PreH4 : (((i * width) + j) >= INT_MIN)) (PreH5 : (j ≠ (0 : Int))) (PreH6 : (i ≠ (0 : Int))) (PreH7 : ((0 : Int) <= ((i * width) + j))) (PreH8 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (width <= INT_MAX)) (PreH12 : (capacity_pre <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (width >= INT_MIN)) (PreH17 : (capacity_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (j <= capacity_pre)) (PreH20 : (width = (capacity_pre + 1))) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 300)) (PreH23 : ((0 : Int) <= capacity_pre)) (PreH24 : (capacity_pre <= 300)) (PreH25 : ((0 : Int) <= i)) (PreH26 : (i <= n_pre)) (PreH27 : ((0 : Int) <= j)) (PreH28 : (j <= (capacity_pre + 1))) (PreH29 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= (((i - 1) * width) + j)) ” &&
  “ ((((i - 1) * width) + j) < ((i * width) + j)) ” &&
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX) ” &&
  “ ((i - 1) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((i - 1) <= INT_MAX)) (PreH2 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH3 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH4 : ((i - 1) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH7 : ((0 : Int) <= (i - 1))) (PreH8 : ((i - 1) < n_pre)) (PreH9 : (((i * width) + j) <= INT_MAX)) (PreH10 : (((i * width) + j) >= INT_MIN)) (PreH11 : (j ≠ (0 : Int))) (PreH12 : (i ≠ (0 : Int))) (PreH13 : ((0 : Int) <= ((i * width) + j))) (PreH14 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : ((0 : Int) <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= n_pre)) (PreH33 : ((0 : Int) <= j)) (PreH34 : (j <= (capacity_pre + 1))) (PreH35 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  TT && emp 
|--
  “ ((((i - 1) * (capacity_pre + 1)) + j) < ((i * (capacity_pre + 1)) + j)) ”
  &&  emp
)

noncomputable def zeroOneKnapsack_entail_wit_5_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((i - 1) <= INT_MAX)) (PreH2 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH3 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH4 : ((i - 1) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH7 : ((0 : Int) <= (i - 1))) (PreH8 : ((i - 1) < n_pre)) (PreH9 : (((i * width) + j) <= INT_MAX)) (PreH10 : (((i * width) + j) >= INT_MIN)) (PreH11 : (j ≠ (0 : Int))) (PreH12 : (i ≠ (0 : Int))) (PreH13 : ((0 : Int) <= ((i * width) + j))) (PreH14 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : ((0 : Int) <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= n_pre)) (PreH33 : ((0 : Int) <= j)) (PreH34 : (j <= (capacity_pre + 1))) (PreH35 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((((i - 1) * (capacity_pre + 1)) + j) < ((i * (capacity_pre + 1)) + j))

noncomputable def zeroOneKnapsack_entail_wit_6 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH2 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH3 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH4 : ((i - 1) <= INT_MAX)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH6 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH7 : ((i - 1) >= INT_MIN)) (PreH8 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH9 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : (((i * width) + j) <= INT_MAX)) (PreH13 : (((i * width) + j) >= INT_MIN)) (PreH14 : (j ≠ (0 : Int))) (PreH15 : (i ≠ (0 : Int))) (PreH16 : ((0 : Int) <= ((i * width) + j))) (PreH17 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1))) (PreH30 : ((0 : Int) <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : ((0 : Int) <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : ((0 : Int) <= i)) (PreH35 : (i <= n_pre)) (PreH36 : ((0 : Int) <= j)) (PreH37 : (j <= (capacity_pre + 1))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int))))) ” &&
  “ ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j)) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= j) ” &&
  “ ((0 : Int) <= (((i - 1) * width) + j)) ” &&
  “ ((((i - 1) * width) + j) < ((i * width) + j)) ” &&
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX) ” &&
  “ ((i - 1) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "w" ) )) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** ((( &( "without" ) )) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "item" ) )) # Int |-> ((i - 1)))
  ** ((( &( "idx" ) )) # Int |-> (((i * width) + j)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH2 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH3 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH4 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH5 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH6 : ((i - 1) <= INT_MAX)) (PreH7 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH8 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH9 : ((i - 1) >= INT_MIN)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : (((i * width) + j) <= INT_MAX)) (PreH15 : (((i * width) + j) >= INT_MIN)) (PreH16 : (j ≠ (0 : Int))) (PreH17 : (i ≠ (0 : Int))) (PreH18 : ((0 : Int) <= ((i * width) + j))) (PreH19 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1))) (PreH32 : ((0 : Int) <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : ((0 : Int) <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : ((0 : Int) <= i)) (PreH37 : (i <= n_pre)) (PreH38 : ((0 : Int) <= j)) (PreH39 : (j <= (capacity_pre + 1))) (PreH40 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  TT && emp 
|--
  “ ((((i - 1) * (capacity_pre + 1)) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * (capacity_pre + 1)) + j)) ”
  &&  emp
)

noncomputable def zeroOneKnapsack_entail_wit_6_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH2 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH3 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH4 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH5 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH6 : ((i - 1) <= INT_MAX)) (PreH7 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH8 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH9 : ((i - 1) >= INT_MIN)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : (((i * width) + j) <= INT_MAX)) (PreH15 : (((i * width) + j) >= INT_MIN)) (PreH16 : (j ≠ (0 : Int))) (PreH17 : (i ≠ (0 : Int))) (PreH18 : ((0 : Int) <= ((i * width) + j))) (PreH19 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1))) (PreH32 : ((0 : Int) <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : ((0 : Int) <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : ((0 : Int) <= i)) (PreH37 : (i <= n_pre)) (PreH38 : ((0 : Int) <= j)) (PreH39 : (j <= (capacity_pre + 1))) (PreH40 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  ((((i - 1) * (capacity_pre + 1)) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * (capacity_pre + 1)) + j))

noncomputable def zeroOneKnapsack_entail_wit_7_1 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (i = (0 : Int))) (PreH2 : ((0 : Int) <= ((i * width) + j))) (PreH3 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1))) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : ((0 : Int) <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (capacity_pre + 1))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + (j + 1)) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (i = (0 : Int))) (PreH2 : ((0 : Int) <= ((i * width) + j))) (PreH3 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1))) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : ((0 : Int) <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (capacity_pre + 1))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
)

noncomputable def zeroOneKnapsack_entail_wit_7_2 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + (j + 1)) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
)

noncomputable def zeroOneKnapsack_entail_wit_7_3 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l_2 (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) > (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l_2 (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + (j + 1)) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l_2 (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) > (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l_2 (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) :: (@List.nil Int))))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
)

noncomputable def zeroOneKnapsack_entail_wit_7_4 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l_2 (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + (j + 1)) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l_2 (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) :: (@List.nil Int))))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
)

noncomputable def zeroOneKnapsack_entail_wit_7_5 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((Znth (i - 1) weights_l (0 : Int)) > j)) (PreH2 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH3 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH4 : ((i - 1) <= INT_MAX)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH6 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH7 : ((i - 1) >= INT_MIN)) (PreH8 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH9 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : (((i * width) + j) <= INT_MAX)) (PreH13 : (((i * width) + j) >= INT_MIN)) (PreH14 : (j ≠ (0 : Int))) (PreH15 : (i ≠ (0 : Int))) (PreH16 : ((0 : Int) <= ((i * width) + j))) (PreH17 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1))) (PreH30 : ((0 : Int) <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : ((0 : Int) <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : ((0 : Int) <= i)) (PreH35 : (i <= n_pre)) (PreH36 : ((0 : Int) <= j)) (PreH37 : (j <= (capacity_pre + 1))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + (j + 1)) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((Znth (i - 1) weights_l (0 : Int)) > j)) (PreH2 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH3 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH4 : ((i - 1) <= INT_MAX)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH6 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH7 : ((i - 1) >= INT_MIN)) (PreH8 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH9 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : (((i * width) + j) <= INT_MAX)) (PreH13 : (((i * width) + j) >= INT_MIN)) (PreH14 : (j ≠ (0 : Int))) (PreH15 : (i ≠ (0 : Int))) (PreH16 : ((0 : Int) <= ((i * width) + j))) (PreH17 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1))) (PreH30 : ((0 : Int) <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : ((0 : Int) <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : ((0 : Int) <= i)) (PreH35 : (i <= n_pre)) (PreH36 : ((0 : Int) <= j)) (PreH37 : (j <= (capacity_pre + 1))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) (((i * width) + j) + 1) (dp_l_2 ++ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l_2 (0 : Int)) :: (@List.nil Int))))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * width) + (j + 1)) dp_l)
)

noncomputable def zeroOneKnapsack_entail_wit_8 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (capacity_pre + 1))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l_2)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l (i + 1)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i + 1) * width) dp_l)
  ** (intArray.undef_seg dp_pre ((i + 1) * width) ((n_pre + 1) * (capacity_pre + 1)))
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (capacity_pre + 1))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j)) ,
  (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l_2)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l (i + 1)) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i + 1) * width) dp_l)
  ** (intArray.undef_seg dp_pre ((i + 1) * width) ((n_pre + 1) * (capacity_pre + 1)))
)

noncomputable def zeroOneKnapsack_entail_wit_9 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (width : Int) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) (i * width) dp_l_2)
  ** (intArray.undef_seg dp_pre (i * width) ((n_pre + 1) * (capacity_pre + 1)))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (width : Int) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i)) ,
  (intArray.seg dp_pre (0 : Int) (i * width) dp_l_2)
  ** (intArray.undef_seg dp_pre (i * width) ((n_pre + 1) * (capacity_pre + 1)))
|--
  EX dp_l : (List Int),
  “ (width = (capacity_pre + 1)) ” &&
  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int))) ”
  &&  (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
)

noncomputable def zeroOneKnapsack_entail_wit_10 : Prop :=
  (
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : (width = (capacity_pre + 1))) (PreH2 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ ((0 : Int) <= ((n_pre * width) + capacity_pre)) ” &&
  “ (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int))) ”
  &&  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : (width <= INT_MAX)) (PreH2 : (capacity_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (width >= INT_MIN)) (PreH5 : (capacity_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (width = (capacity_pre + 1))) (PreH8 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  TT && emp 
|--
  “ (((n_pre * (capacity_pre + 1)) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ ((0 : Int) <= ((n_pre * (capacity_pre + 1)) + capacity_pre)) ”
  &&  emp
)

noncomputable def zeroOneKnapsack_entail_wit_10_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : (width <= INT_MAX)) (PreH2 : (capacity_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (width >= INT_MIN)) (PreH5 : (capacity_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (width = (capacity_pre + 1))) (PreH8 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  (((n_pre * (capacity_pre + 1)) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))

noncomputable def zeroOneKnapsack_entail_wit_10_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : (width <= INT_MAX)) (PreH2 : (capacity_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (width >= INT_MIN)) (PreH5 : (capacity_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (width = (capacity_pre + 1))) (PreH8 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  ((0 : Int) <= ((n_pre * (capacity_pre + 1)) + capacity_pre))

noncomputable def zeroOneKnapsack_return_wit_1 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l_2 (Znth ((n_pre * width) + capacity_pre) dp_l_2 (0 : Int)))) ,
  (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
|--
  EX dp_l : (List Int),
  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l_2 (0 : Int))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)

noncomputable def zeroOneKnapsack_partial_solve_wit_1 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (i = (0 : Int))) (PreH2 : ((0 : Int) <= ((i * width) + j))) (PreH3 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1))) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : ((0 : Int) <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i <= n_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (capacity_pre + 1))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (i = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((dp_pre + (((i * width) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)

noncomputable def zeroOneKnapsack_partial_solve_wit_2 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : ((0 : Int) <= ((i * width) + j))) (PreH4 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : ((0 : Int) <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i <= n_pre)) (PreH23 : ((0 : Int) <= j)) (PreH24 : (j <= (capacity_pre + 1))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (j = (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((dp_pre + (((i * width) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)

noncomputable def zeroOneKnapsack_partial_solve_wit_3 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : (((i * width) + j) <= INT_MAX)) (PreH4 : (((i * width) + j) >= INT_MIN)) (PreH5 : (j ≠ (0 : Int))) (PreH6 : (i ≠ (0 : Int))) (PreH7 : ((0 : Int) <= ((i * width) + j))) (PreH8 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (width <= INT_MAX)) (PreH12 : (capacity_pre <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (width >= INT_MIN)) (PreH17 : (capacity_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (j <= capacity_pre)) (PreH20 : (width = (capacity_pre + 1))) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 300)) (PreH23 : ((0 : Int) <= capacity_pre)) (PreH24 : (capacity_pre <= 300)) (PreH25 : ((0 : Int) <= i)) (PreH26 : (i <= n_pre)) (PreH27 : ((0 : Int) <= j)) (PreH28 : (j <= (capacity_pre + 1))) (PreH29 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((weights_pre + ((i - 1) * sizeof(INT)))) # Int |-> ((Znth (i - 1) weights_l (0 : Int))))
  ** (intArray.missing_i weights_pre (i - 1) (0 : Int) n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))

noncomputable def zeroOneKnapsack_partial_solve_wit_4 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : (((i * width) + j) <= INT_MAX)) (PreH4 : (((i * width) + j) >= INT_MIN)) (PreH5 : (j ≠ (0 : Int))) (PreH6 : (i ≠ (0 : Int))) (PreH7 : ((0 : Int) <= ((i * width) + j))) (PreH8 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (width <= INT_MAX)) (PreH12 : (capacity_pre <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (width >= INT_MIN)) (PreH17 : (capacity_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (j <= capacity_pre)) (PreH20 : (width = (capacity_pre + 1))) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 300)) (PreH23 : ((0 : Int) <= capacity_pre)) (PreH24 : (capacity_pre <= 300)) (PreH25 : ((0 : Int) <= i)) (PreH26 : (i <= n_pre)) (PreH27 : ((0 : Int) <= j)) (PreH28 : (j <= (capacity_pre + 1))) (PreH29 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((values_pre + ((i - 1) * sizeof(INT)))) # Int |-> ((Znth (i - 1) values_l (0 : Int))))
  ** (intArray.missing_i values_pre (i - 1) (0 : Int) n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))

noncomputable def zeroOneKnapsack_partial_solve_wit_5 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH2 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH3 : ((i - 1) <= INT_MAX)) (PreH4 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH6 : ((i - 1) >= INT_MIN)) (PreH7 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH8 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH9 : ((0 : Int) <= (i - 1))) (PreH10 : ((i - 1) < n_pre)) (PreH11 : (((i * width) + j) <= INT_MAX)) (PreH12 : (((i * width) + j) >= INT_MIN)) (PreH13 : (j ≠ (0 : Int))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : ((0 : Int) <= ((i * width) + j))) (PreH16 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : ((0 : Int) <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i <= n_pre)) (PreH35 : ((0 : Int) <= j)) (PreH36 : (j <= (capacity_pre + 1))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= (((i - 1) * width) + j)) ” &&
  “ ((((i - 1) * width) + j) < ((i * width) + j)) ” &&
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX) ” &&
  “ ((i - 1) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((dp_pre + ((((i - 1) * width) + j) * sizeof(INT)))) # Int |-> ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre (((i - 1) * width) + j) (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))

noncomputable def zeroOneKnapsack_partial_solve_wit_6 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH2 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH3 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH6 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH7 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH8 : ((i - 1) <= INT_MAX)) (PreH9 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH10 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH11 : ((i - 1) >= INT_MIN)) (PreH12 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH13 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH14 : ((0 : Int) <= (i - 1))) (PreH15 : ((i - 1) < n_pre)) (PreH16 : (((i * width) + j) <= INT_MAX)) (PreH17 : (((i * width) + j) >= INT_MIN)) (PreH18 : (j ≠ (0 : Int))) (PreH19 : (i ≠ (0 : Int))) (PreH20 : ((0 : Int) <= ((i * width) + j))) (PreH21 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1))) (PreH34 : ((0 : Int) <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : ((0 : Int) <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i <= n_pre)) (PreH40 : ((0 : Int) <= j)) (PreH41 : (j <= (capacity_pre + 1))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int))))) ” &&
  “ ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j)) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= j) ” &&
  “ ((0 : Int) <= (((i - 1) * width) + j)) ” &&
  “ ((((i - 1) * width) + j) < ((i * width) + j)) ” &&
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX) ” &&
  “ ((i - 1) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((dp_pre + ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) * sizeof(INT)))) # Int |-> ((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))

noncomputable def zeroOneKnapsack_partial_solve_wit_7 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) > (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) > (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))) ” &&
  “ ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int))))) ” &&
  “ ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j)) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= j) ” &&
  “ ((0 : Int) <= (((i - 1) * width) + j)) ” &&
  “ ((((i - 1) * width) + j) < ((i * width) + j)) ” &&
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX) ” &&
  “ ((i - 1) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((dp_pre + (((i * width) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def zeroOneKnapsack_partial_solve_wit_8 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)))) (PreH2 : ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))))) (PreH3 : ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j))) (PreH4 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN)) (PreH6 : ((Znth (i - 1) weights_l (0 : Int)) <= j)) (PreH7 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH8 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH9 : ((i - 1) <= INT_MAX)) (PreH10 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH12 : ((i - 1) >= INT_MIN)) (PreH13 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH14 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : (((i * width) + j) <= INT_MAX)) (PreH18 : (((i * width) + j) >= INT_MIN)) (PreH19 : (j ≠ (0 : Int))) (PreH20 : (i ≠ (0 : Int))) (PreH21 : ((0 : Int) <= ((i * width) + j))) (PreH22 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1))) (PreH35 : ((0 : Int) <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : ((0 : Int) <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : ((0 : Int) <= i)) (PreH40 : (i <= n_pre)) (PreH41 : ((0 : Int) <= j)) (PreH42 : (j <= (capacity_pre + 1))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ (((Znth ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) - (0 : Int)) dp_l (0 : Int)) + (Znth (i - 1) values_l (0 : Int))) <= (Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int))) ” &&
  “ ((0 : Int) <= (((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int))))) ” &&
  “ ((((i - 1) * width) + (j - (Znth (i - 1) weights_l (0 : Int)))) < ((i * width) + j)) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth ((((i - 1) * width) + j) - (0 : Int)) dp_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= j) ” &&
  “ ((0 : Int) <= (((i - 1) * width) + j)) ” &&
  “ ((((i - 1) * width) + j) < ((i * width) + j)) ” &&
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX) ” &&
  “ ((i - 1) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((dp_pre + (((i * width) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def zeroOneKnapsack_partial_solve_wit_9 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (width : Int) (PreH1 : ((Znth (i - 1) weights_l (0 : Int)) > j)) (PreH2 : ((0 : Int) <= (((i - 1) * width) + j))) (PreH3 : ((((i - 1) * width) + j) < ((i * width) + j))) (PreH4 : ((i - 1) <= INT_MAX)) (PreH5 : ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX)) (PreH6 : ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX)) (PreH7 : ((i - 1) >= INT_MIN)) (PreH8 : ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN)) (PreH9 : ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN)) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : (((i * width) + j) <= INT_MAX)) (PreH13 : (((i * width) + j) >= INT_MIN)) (PreH14 : (j ≠ (0 : Int))) (PreH15 : (i ≠ (0 : Int))) (PreH16 : ((0 : Int) <= ((i * width) + j))) (PreH17 : (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1))) (PreH30 : ((0 : Int) <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : ((0 : Int) <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : ((0 : Int) <= i)) (PreH35 : (i <= n_pre)) (PreH36 : ((0 : Int) <= j)) (PreH37 : (j <= (capacity_pre + 1))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j)) ,
  (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg dp_pre ((i * width) + j) ((n_pre + 1) * (capacity_pre + 1)))
|--
  “ ((Znth (i - 1) weights_l (0 : Int)) > j) ” &&
  “ ((0 : Int) <= (((i - 1) * width) + j)) ” &&
  “ ((((i - 1) * width) + j) < ((i * width) + j)) ” &&
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) <= INT_MAX) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) <= INT_MAX) ” &&
  “ ((i - 1) >= INT_MIN) ” &&
  “ ((Znth (i - 1) weights_l (0 : Int)) >= INT_MIN) ” &&
  “ ((Znth (i - 1) values_l (0 : Int)) >= INT_MIN) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (((i * width) + j) <= INT_MAX) ” &&
  “ (((i * width) + j) >= INT_MIN) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * width) + j)) ” &&
  “ (((i * width) + j) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (j <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (width <= INT_MAX) ” &&
  “ (capacity_pre <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (j >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (width >= INT_MIN) ” &&
  “ (capacity_pre >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= capacity_pre) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 300) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 300) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j) ”
  &&  (((dp_pre + (((i * width) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (((i * width) + j) + 1) ((n_pre + 1) * (capacity_pre + 1)))
  ** (intArray.seg dp_pre (0 : Int) ((i * width) + j) dp_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def zeroOneKnapsack_partial_solve_wit_10 : Prop :=
  forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (values_pre : Int) (weights_pre : Int) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (width : Int) (PreH1 : ((0 : Int) <= ((n_pre * width) + capacity_pre))) (PreH2 : (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1)))) (PreH3 : (width = (capacity_pre + 1))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l)
|--
  “ ((0 : Int) <= ((n_pre * width) + capacity_pre)) ” &&
  “ (((n_pre * width) + capacity_pre) < ((n_pre + 1) * (capacity_pre + 1))) ” &&
  “ (width = (capacity_pre + 1)) ” &&
  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int))) ”
  &&  (((dp_pre + (((n_pre * width) + capacity_pre) * sizeof(INT)))) # Int |-> ((Znth ((n_pre * width) + capacity_pre) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre ((n_pre * width) + capacity_pre) (0 : Int) ((n_pre + 1) * (capacity_pre + 1)) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)


structure VC_Correct : Type where
  proof_of_zeroOneKnapsack_safety_wit_1 : zeroOneKnapsack_safety_wit_1
  proof_of_zeroOneKnapsack_safety_wit_2 : zeroOneKnapsack_safety_wit_2
  proof_of_zeroOneKnapsack_safety_wit_3 : zeroOneKnapsack_safety_wit_3
  proof_of_zeroOneKnapsack_safety_wit_4 : zeroOneKnapsack_safety_wit_4
  proof_of_zeroOneKnapsack_safety_wit_5 : zeroOneKnapsack_safety_wit_5
  proof_of_zeroOneKnapsack_safety_wit_6 : zeroOneKnapsack_safety_wit_6
  proof_of_zeroOneKnapsack_safety_wit_7 : zeroOneKnapsack_safety_wit_7
  proof_of_zeroOneKnapsack_safety_wit_8 : zeroOneKnapsack_safety_wit_8
  proof_of_zeroOneKnapsack_safety_wit_9 : zeroOneKnapsack_safety_wit_9
  proof_of_zeroOneKnapsack_safety_wit_10 : zeroOneKnapsack_safety_wit_10
  proof_of_zeroOneKnapsack_safety_wit_11 : zeroOneKnapsack_safety_wit_11
  proof_of_zeroOneKnapsack_safety_wit_12 : zeroOneKnapsack_safety_wit_12
  proof_of_zeroOneKnapsack_safety_wit_13 : zeroOneKnapsack_safety_wit_13
  proof_of_zeroOneKnapsack_safety_wit_14 : zeroOneKnapsack_safety_wit_14
  proof_of_zeroOneKnapsack_safety_wit_15 : zeroOneKnapsack_safety_wit_15
  proof_of_zeroOneKnapsack_safety_wit_16 : zeroOneKnapsack_safety_wit_16
  proof_of_zeroOneKnapsack_safety_wit_17 : zeroOneKnapsack_safety_wit_17
  proof_of_zeroOneKnapsack_safety_wit_18 : zeroOneKnapsack_safety_wit_18
  proof_of_zeroOneKnapsack_safety_wit_19 : zeroOneKnapsack_safety_wit_19
  proof_of_zeroOneKnapsack_safety_wit_20 : zeroOneKnapsack_safety_wit_20
  proof_of_zeroOneKnapsack_safety_wit_21 : zeroOneKnapsack_safety_wit_21
  proof_of_zeroOneKnapsack_safety_wit_23 : zeroOneKnapsack_safety_wit_23
  proof_of_zeroOneKnapsack_safety_wit_24 : zeroOneKnapsack_safety_wit_24
  proof_of_zeroOneKnapsack_safety_wit_25 : zeroOneKnapsack_safety_wit_25
  proof_of_zeroOneKnapsack_safety_wit_26 : zeroOneKnapsack_safety_wit_26
  proof_of_zeroOneKnapsack_safety_wit_27 : zeroOneKnapsack_safety_wit_27
  proof_of_zeroOneKnapsack_safety_wit_28 : zeroOneKnapsack_safety_wit_28
  proof_of_zeroOneKnapsack_entail_wit_4 : zeroOneKnapsack_entail_wit_4
  proof_of_zeroOneKnapsack_return_wit_1 : zeroOneKnapsack_return_wit_1
  proof_of_zeroOneKnapsack_partial_solve_wit_1 : zeroOneKnapsack_partial_solve_wit_1
  proof_of_zeroOneKnapsack_partial_solve_wit_2 : zeroOneKnapsack_partial_solve_wit_2
  proof_of_zeroOneKnapsack_partial_solve_wit_3 : zeroOneKnapsack_partial_solve_wit_3
  proof_of_zeroOneKnapsack_partial_solve_wit_4 : zeroOneKnapsack_partial_solve_wit_4
  proof_of_zeroOneKnapsack_partial_solve_wit_5 : zeroOneKnapsack_partial_solve_wit_5
  proof_of_zeroOneKnapsack_partial_solve_wit_6 : zeroOneKnapsack_partial_solve_wit_6
  proof_of_zeroOneKnapsack_partial_solve_wit_7 : zeroOneKnapsack_partial_solve_wit_7
  proof_of_zeroOneKnapsack_partial_solve_wit_8 : zeroOneKnapsack_partial_solve_wit_8
  proof_of_zeroOneKnapsack_partial_solve_wit_9 : zeroOneKnapsack_partial_solve_wit_9
  proof_of_zeroOneKnapsack_partial_solve_wit_10 : zeroOneKnapsack_partial_solve_wit_10
  proof_of_zeroOneKnapsack_safety_wit_22 : zeroOneKnapsack_safety_wit_22
  proof_of_zeroOneKnapsack_safety_wit_29 : zeroOneKnapsack_safety_wit_29
  proof_of_zeroOneKnapsack_safety_wit_30 : zeroOneKnapsack_safety_wit_30
  proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1
  proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2
  proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3
  proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5
  proof_of_zeroOneKnapsack_entail_wit_6 : zeroOneKnapsack_entail_wit_6
  proof_of_zeroOneKnapsack_entail_wit_7_1 : zeroOneKnapsack_entail_wit_7_1
  proof_of_zeroOneKnapsack_entail_wit_7_2 : zeroOneKnapsack_entail_wit_7_2
  proof_of_zeroOneKnapsack_entail_wit_7_3 : zeroOneKnapsack_entail_wit_7_3
  proof_of_zeroOneKnapsack_entail_wit_7_4 : zeroOneKnapsack_entail_wit_7_4
  proof_of_zeroOneKnapsack_entail_wit_7_5 : zeroOneKnapsack_entail_wit_7_5
  proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8
  proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9
  proof_of_zeroOneKnapsack_entail_wit_10 : zeroOneKnapsack_entail_wit_10

end SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_goal
