import SimpleC.SL.SeparationLogic

import Algorithms.matrix_chain_multiplication.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance matrix_chain_multiplication_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def matrixChainMinCost_safety_wit_1 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_full cost_pre (matrix_count_pre * matrix_count_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def matrixChainMinCost_safety_wit_2 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (i : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH6 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH7 : (MatrixChainZeroPrefix cost_l i)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg cost_pre (0 : Int) i cost_l)
  ** (intArray.undef_seg cost_pre i (matrix_count_pre * matrix_count_pre))
|--
  “ ((matrix_count_pre * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (matrix_count_pre * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_3 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l i)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg cost_pre (0 : Int) i cost_l)
  ** (intArray.undef_seg cost_pre i (matrix_count_pre * matrix_count_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def matrixChainMinCost_safety_wit_4 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l i)) ,
  (intArray.seg cost_pre (0 : Int) (i + 1) (cost_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg cost_pre (i + 1) (matrix_count_pre * matrix_count_pre))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_5 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH5 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH6 : (MatrixChainTableValuesBounded cost_l)) (PreH7 : (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre 2)) ,
  ((( &( "chain_length" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def matrixChainMinCost_safety_wit_6 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre chain_length)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def matrixChainMinCost_safety_wit_7 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH5 : (2 <= chain_length)) (PreH6 : (chain_length <= matrix_count_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH9 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH10 : (MatrixChainTableValuesBounded cost_l)) (PreH11 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((left + chain_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + chain_length)) ”

noncomputable def matrixChainMinCost_safety_wit_8 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (((left + chain_length) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + chain_length) - 1)) ”

noncomputable def matrixChainMinCost_safety_wit_9 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((left + chain_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + chain_length)) ”

noncomputable def matrixChainMinCost_safety_wit_10 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_11 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ”

noncomputable def matrixChainMinCost_safety_wit_12 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_13 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((right + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_14 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_15 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_16 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_17 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ ((((left + 1) * matrix_count_pre) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((left + 1) * matrix_count_pre) + right)) ”

noncomputable def matrixChainMinCost_safety_wit_18 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (((left + 1) * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + 1) * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_19 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_20 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (((left * matrix_count_pre) + left) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * matrix_count_pre) + left)) ”

noncomputable def matrixChainMinCost_safety_wit_21 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((left * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_22 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_23 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_24 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_25 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "split" ) )) # Int |->_)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |-> ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_26 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "split" ) )) # Int |->_)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |-> ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_27 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ”

noncomputable def matrixChainMinCost_safety_wit_28 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_29 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((right + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_30 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_31 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_32 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_33 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ ((((split + 1) * matrix_count_pre) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((split + 1) * matrix_count_pre) + right)) ”

noncomputable def matrixChainMinCost_safety_wit_34 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (((split + 1) * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((split + 1) * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_35 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_36 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (((left * matrix_count_pre) + split) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * matrix_count_pre) + split)) ”

noncomputable def matrixChainMinCost_safety_wit_37 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((left * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_38 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_39 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_40 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_41 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (candidate))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_42 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_43 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (((left * matrix_count_pre) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * matrix_count_pre) + right)) ”

noncomputable def matrixChainMinCost_safety_wit_44 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((left * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_45 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) (replace_Znth (((left * matrix_count_pre) + right)) (best) (cost_l)))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_46 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((chain_length + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (chain_length + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_47 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((0 : Int) <= (matrix_count_pre - 1))) (PreH4 : ((matrix_count_pre - 1) < (matrix_count_pre * matrix_count_pre))) (PreH5 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH6 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH7 : ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l (0 : Int)))) (PreH8 : ((Znth (matrix_count_pre - 1) cost_l (0 : Int)) <= 7000000)) (PreH9 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH10 : (MatrixChainTableValuesBounded cost_l)) (PreH11 : (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre (matrix_count_pre + 1))) (PreH12 : (MatrixChainTableResult dimensions_l cost_l matrix_count_pre)) (PreH13 : (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int)))) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ ((matrix_count_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (matrix_count_pre - 1)) ”

noncomputable def matrixChainMinCost_safety_wit_48 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((0 : Int) <= (matrix_count_pre - 1))) (PreH4 : ((matrix_count_pre - 1) < (matrix_count_pre * matrix_count_pre))) (PreH5 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH6 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH7 : ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l (0 : Int)))) (PreH8 : ((Znth (matrix_count_pre - 1) cost_l (0 : Int)) <= 7000000)) (PreH9 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH10 : (MatrixChainTableValuesBounded cost_l)) (PreH11 : (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre (matrix_count_pre + 1))) (PreH12 : (MatrixChainTableResult dimensions_l cost_l matrix_count_pre)) (PreH13 : (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int)))) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "cost" ) )) # Ptr |-> (cost_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_entail_wit_1 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_full cost_pre (matrix_count_pre * matrix_count_pre))
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainZeroPrefix cost_l (0 : Int)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg cost_pre (0 : Int) (0 : Int) cost_l)
  ** (intArray.undef_seg cost_pre (0 : Int) (matrix_count_pre * matrix_count_pre))
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) ,
  TT && emp 
|--
  “ (MatrixChainZeroPrefix (@List.nil Int) (0 : Int)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_1_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) ,
  (MatrixChainZeroPrefix (@List.nil Int) (0 : Int))

noncomputable def matrixChainMinCost_entail_wit_2 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i)) ,
  (intArray.seg cost_pre (0 : Int) (i + 1) (cost_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg cost_pre (i + 1) (matrix_count_pre * matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainZeroPrefix cost_l (i + 1)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg cost_pre (0 : Int) (i + 1) cost_l)
  ** (intArray.undef_seg cost_pre (i + 1) (matrix_count_pre * matrix_count_pre))
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i)) ,
  TT && emp 
|--
  “ (MatrixChainZeroPrefix (cost_l_2 ++ ((0 : Int) :: (@List.nil Int))) (i + 1)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_2_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i)) ,
  (MatrixChainZeroPrefix (cost_l_2 ++ ((0 : Int) :: (@List.nil Int))) (i + 1))

noncomputable def matrixChainMinCost_entail_wit_3 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg cost_pre (0 : Int) i cost_l_2)
  ** (intArray.undef_seg cost_pre i (matrix_count_pre * matrix_count_pre))
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre 2) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i)) ,
  (intArray.seg cost_pre (0 : Int) i cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre 2) ”
  &&  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
)

noncomputable def matrixChainMinCost_entail_wit_4 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH5 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH6 : (MatrixChainTableValuesBounded cost_l_2)) (PreH7 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre 2)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (matrix_count_pre + 1)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre 2) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_entail_wit_5 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((matrix_count_pre - chain_length) + 1)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length (0 : Int)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  TT && emp 
|--
  “ (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length (0 : Int)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length (0 : Int))

noncomputable def matrixChainMinCost_entail_wit_6 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (((left + chain_length) - 1) = ((left + chain_length) - 1)) ” &&
  “ (left < ((left + chain_length) - 1)) ” &&
  “ (((left + chain_length) - 1) < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))) ” &&
  “ ((((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (((left + chain_length) - 1) + 1)) ” &&
  “ ((((left + chain_length) - 1) + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  TT && emp 
|--
  “ ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int))) ” &&
  “ ((((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_2 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_3 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_4 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (1 <= (Znth (left + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_5 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth left dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_6 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (1 <= (Znth left dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_7 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_8 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_9 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_10 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_11 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_12 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_7 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  EX cost_l_2 : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= (left + 1)) ” &&
  “ ((left + 1) <= right) ” &&
  “ ((0 : Int) <= (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l_2) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (left + 1) (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  TT && emp 
|--
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1) (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1) (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))))

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_2 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_8 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int))) ” &&
  “ ((((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_2 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_3 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_4 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (1 <= (Znth (split + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_5 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth left dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_6 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (1 <= (Znth left dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_7 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_8 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_9 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_10 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_11 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_12 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_9 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  EX cost_l_2 : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((0 : Int) <= (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l_2) ” &&
  “ (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length) - 1) split (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_9_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length) - 1) split (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))))

noncomputable def matrixChainMinCost_entail_wit_9_split_goal_2 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_10_1 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l_2)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (split + 1) candidate) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l_2)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) candidate) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_10_1_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l_2)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) candidate)

noncomputable def matrixChainMinCost_entail_wit_10_2 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l_2)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (split + 1) best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l_2)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) best) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_10_2_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH20 : (MatrixChainTableValuesBounded cost_l_2)) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) best)

noncomputable def matrixChainMinCost_entail_wit_11 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + right)) ” &&
  “ (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best) ” &&
  “ (MatrixChainIntervalMinimum dimensions_l left right best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length) - 1) best) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length) - 1) best) ” &&
  “ (((left * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_11_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length) - 1) best)

noncomputable def matrixChainMinCost_entail_wit_11_split_goal_2 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length) - 1) best)

noncomputable def matrixChainMinCost_entail_wit_11_split_goal_3 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH18 : (MatrixChainTableValuesBounded cost_l_2)) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (((left * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_12 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l_2)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) (replace_Znth (((left * matrix_count_pre) + right)) (best) (cost_l_2)))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= ((matrix_count_pre - chain_length) + 1)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length (left + 1)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l_2)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  TT && emp 
|--
  “ (MatrixChainLeftProgress dimensions_l (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1)) ” &&
  “ (MatrixChainTableValuesBounded (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2))) ” &&
  “ ((Zlength ((replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_12_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l_2)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (MatrixChainLeftProgress dimensions_l (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1))

noncomputable def matrixChainMinCost_entail_wit_12_split_goal_2 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l_2)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (MatrixChainTableValuesBounded (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)))

noncomputable def matrixChainMinCost_entail_wit_12_split_goal_3 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l_2)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  ((Zlength ((replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_13 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= (chain_length + 1)) ” &&
  “ ((chain_length + 1) <= (matrix_count_pre + 1)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre (chain_length + 1)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  TT && emp 
|--
  “ (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (chain_length + 1)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_13_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH11 : (MatrixChainTableValuesBounded cost_l_2)) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (chain_length + 1))

noncomputable def matrixChainMinCost_entail_wit_14 : Prop :=
  (
forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((0 : Int) <= (matrix_count_pre - 1)) ” &&
  “ ((matrix_count_pre - 1) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ” &&
  “ ((Znth (matrix_count_pre - 1) cost_l (0 : Int)) <= 7000000) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre (matrix_count_pre + 1)) ” &&
  “ (MatrixChainTableResult dimensions_l cost_l matrix_count_pre) ” &&
  “ (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
) \/
(
forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  TT && emp 
|--
  “ (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int))) ” &&
  “ (MatrixChainTableResult dimensions_l cost_l_2 matrix_count_pre) ” &&
  “ (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (matrix_count_pre + 1)) ” &&
  “ ((Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int))) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_14_split_goal_1 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_14_split_goal_2 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (MatrixChainTableResult dimensions_l cost_l_2 matrix_count_pre)

noncomputable def matrixChainMinCost_entail_wit_14_split_goal_3 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (matrix_count_pre + 1))

noncomputable def matrixChainMinCost_entail_wit_14_split_goal_4 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  ((Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_14_split_goal_5 : Prop :=
  forall (matrix_count_pre : Int) (dimensions_l : (List Int)) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH9 : (MatrixChainTableValuesBounded cost_l_2)) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_return_wit_1 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l_2 : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((0 : Int) <= (matrix_count_pre - 1))) (PreH4 : ((matrix_count_pre - 1) < (matrix_count_pre * matrix_count_pre))) (PreH5 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH6 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH7 : ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)))) (PreH8 : ((Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)) <= 7000000)) (PreH9 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH10 : (MatrixChainTableValuesBounded cost_l_2)) (PreH11 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (matrix_count_pre + 1))) (PreH12 : (MatrixChainTableResult dimensions_l cost_l_2 matrix_count_pre)) (PreH13 : (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)))) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  EX cost_l : (List Int),
  “ (MatrixChainTableResult dimensions_l cost_l matrix_count_pre) ” &&
  “ (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int))) ” &&
  “ ((Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)) = (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l_2 (0 : Int))) ” &&
  “ ((Znth (matrix_count_pre - 1) cost_l_2 (0 : Int)) <= 7000000) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_1 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH8 : (MatrixChainZeroPrefix cost_l i)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg cost_pre (0 : Int) i cost_l)
  ** (intArray.undef_seg cost_pre i (matrix_count_pre * matrix_count_pre))
|--
  “ (i < (matrix_count_pre * matrix_count_pre)) ” &&
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainZeroPrefix cost_l i) ”
  &&  (((cost_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg cost_pre (i + 1) (matrix_count_pre * matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg cost_pre (0 : Int) i cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_2 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((cost_pre + (((left * matrix_count_pre) + left) * sizeof(INT)))) # Int |-> ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))))
  ** (intArray.missing_i cost_pre ((left * matrix_count_pre) + left) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)

noncomputable def matrixChainMinCost_partial_solve_wit_3 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((cost_pre + ((((left + 1) * matrix_count_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))))
  ** (intArray.missing_i cost_pre (((left + 1) * matrix_count_pre) + right) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)

noncomputable def matrixChainMinCost_partial_solve_wit_4 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((dimensions_pre + (left * sizeof(INT)))) # Int |-> ((Znth left dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre left (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_5 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((dimensions_pre + ((left + 1) * sizeof(INT)))) # Int |-> ((Znth (left + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (left + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_6 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH33 : (MatrixChainTableValuesBounded cost_l)) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((dimensions_pre + ((right + 1) * sizeof(INT)))) # Int |-> ((Znth (right + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (right + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_7 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((cost_pre + (((left * matrix_count_pre) + split) * sizeof(INT)))) # Int |-> ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))))
  ** (intArray.missing_i cost_pre ((left * matrix_count_pre) + split) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)

noncomputable def matrixChainMinCost_partial_solve_wit_8 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((cost_pre + ((((split + 1) * matrix_count_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))))
  ** (intArray.missing_i cost_pre (((split + 1) * matrix_count_pre) + right) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)

noncomputable def matrixChainMinCost_partial_solve_wit_9 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((dimensions_pre + (left * sizeof(INT)))) # Int |-> ((Znth left dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre left (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_10 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((dimensions_pre + ((split + 1) * sizeof(INT)))) # Int |-> ((Znth (split + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (split + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_11 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH37 : (MatrixChainTableValuesBounded cost_l)) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((dimensions_pre + ((right + 1) * sizeof(INT)))) # Int |-> ((Znth (right + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (right + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)

noncomputable def matrixChainMinCost_partial_solve_wit_12 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH17 : (MatrixChainTableValuesBounded cost_l)) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + right)) ” &&
  “ (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best) ” &&
  “ (MatrixChainIntervalMinimum dimensions_l left right best) ”
  &&  (((cost_pre + (((left * matrix_count_pre) + right) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i cost_pre ((left * matrix_count_pre) + right) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)

noncomputable def matrixChainMinCost_partial_solve_wit_13 : Prop :=
  forall (cost_pre : Int) (matrix_count_pre : Int) (dimensions_pre : Int) (dimensions_l : (List Int)) (cost_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((0 : Int) <= (matrix_count_pre - 1))) (PreH4 : ((matrix_count_pre - 1) < (matrix_count_pre * matrix_count_pre))) (PreH5 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH6 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH7 : ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l (0 : Int)))) (PreH8 : ((Znth (matrix_count_pre - 1) cost_l (0 : Int)) <= 7000000)) (PreH9 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre)) (PreH10 : (MatrixChainTableValuesBounded cost_l)) (PreH11 : (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre (matrix_count_pre + 1))) (PreH12 : (MatrixChainTableResult dimensions_l cost_l matrix_count_pre)) (PreH13 : (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int)))) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full cost_pre (matrix_count_pre * matrix_count_pre) cost_l)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((0 : Int) <= (matrix_count_pre - 1)) ” &&
  “ ((matrix_count_pre - 1) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ” &&
  “ ((Znth (matrix_count_pre - 1) cost_l (0 : Int)) <= 7000000) ” &&
  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre) ” &&
  “ (MatrixChainTableValuesBounded cost_l) ” &&
  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre (matrix_count_pre + 1)) ” &&
  “ (MatrixChainTableResult dimensions_l cost_l matrix_count_pre) ” &&
  “ (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ”
  &&  (((cost_pre + ((matrix_count_pre - 1) * sizeof(INT)))) # Int |-> ((Znth (matrix_count_pre - 1) cost_l (0 : Int))))
  ** (intArray.missing_i cost_pre (matrix_count_pre - 1) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)


structure VC_Correct : Type where
  proof_of_matrixChainMinCost_safety_wit_1 : matrixChainMinCost_safety_wit_1
  proof_of_matrixChainMinCost_safety_wit_2 : matrixChainMinCost_safety_wit_2
  proof_of_matrixChainMinCost_safety_wit_3 : matrixChainMinCost_safety_wit_3
  proof_of_matrixChainMinCost_safety_wit_4 : matrixChainMinCost_safety_wit_4
  proof_of_matrixChainMinCost_safety_wit_5 : matrixChainMinCost_safety_wit_5
  proof_of_matrixChainMinCost_safety_wit_6 : matrixChainMinCost_safety_wit_6
  proof_of_matrixChainMinCost_safety_wit_7 : matrixChainMinCost_safety_wit_7
  proof_of_matrixChainMinCost_safety_wit_8 : matrixChainMinCost_safety_wit_8
  proof_of_matrixChainMinCost_safety_wit_9 : matrixChainMinCost_safety_wit_9
  proof_of_matrixChainMinCost_safety_wit_10 : matrixChainMinCost_safety_wit_10
  proof_of_matrixChainMinCost_safety_wit_11 : matrixChainMinCost_safety_wit_11
  proof_of_matrixChainMinCost_safety_wit_12 : matrixChainMinCost_safety_wit_12
  proof_of_matrixChainMinCost_safety_wit_13 : matrixChainMinCost_safety_wit_13
  proof_of_matrixChainMinCost_safety_wit_14 : matrixChainMinCost_safety_wit_14
  proof_of_matrixChainMinCost_safety_wit_15 : matrixChainMinCost_safety_wit_15
  proof_of_matrixChainMinCost_safety_wit_16 : matrixChainMinCost_safety_wit_16
  proof_of_matrixChainMinCost_safety_wit_17 : matrixChainMinCost_safety_wit_17
  proof_of_matrixChainMinCost_safety_wit_18 : matrixChainMinCost_safety_wit_18
  proof_of_matrixChainMinCost_safety_wit_19 : matrixChainMinCost_safety_wit_19
  proof_of_matrixChainMinCost_safety_wit_20 : matrixChainMinCost_safety_wit_20
  proof_of_matrixChainMinCost_safety_wit_21 : matrixChainMinCost_safety_wit_21
  proof_of_matrixChainMinCost_safety_wit_22 : matrixChainMinCost_safety_wit_22
  proof_of_matrixChainMinCost_safety_wit_23 : matrixChainMinCost_safety_wit_23
  proof_of_matrixChainMinCost_safety_wit_24 : matrixChainMinCost_safety_wit_24
  proof_of_matrixChainMinCost_safety_wit_25 : matrixChainMinCost_safety_wit_25
  proof_of_matrixChainMinCost_safety_wit_26 : matrixChainMinCost_safety_wit_26
  proof_of_matrixChainMinCost_safety_wit_27 : matrixChainMinCost_safety_wit_27
  proof_of_matrixChainMinCost_safety_wit_28 : matrixChainMinCost_safety_wit_28
  proof_of_matrixChainMinCost_safety_wit_29 : matrixChainMinCost_safety_wit_29
  proof_of_matrixChainMinCost_safety_wit_30 : matrixChainMinCost_safety_wit_30
  proof_of_matrixChainMinCost_safety_wit_31 : matrixChainMinCost_safety_wit_31
  proof_of_matrixChainMinCost_safety_wit_32 : matrixChainMinCost_safety_wit_32
  proof_of_matrixChainMinCost_safety_wit_33 : matrixChainMinCost_safety_wit_33
  proof_of_matrixChainMinCost_safety_wit_34 : matrixChainMinCost_safety_wit_34
  proof_of_matrixChainMinCost_safety_wit_35 : matrixChainMinCost_safety_wit_35
  proof_of_matrixChainMinCost_safety_wit_36 : matrixChainMinCost_safety_wit_36
  proof_of_matrixChainMinCost_safety_wit_37 : matrixChainMinCost_safety_wit_37
  proof_of_matrixChainMinCost_safety_wit_38 : matrixChainMinCost_safety_wit_38
  proof_of_matrixChainMinCost_safety_wit_39 : matrixChainMinCost_safety_wit_39
  proof_of_matrixChainMinCost_safety_wit_40 : matrixChainMinCost_safety_wit_40
  proof_of_matrixChainMinCost_safety_wit_41 : matrixChainMinCost_safety_wit_41
  proof_of_matrixChainMinCost_safety_wit_42 : matrixChainMinCost_safety_wit_42
  proof_of_matrixChainMinCost_safety_wit_43 : matrixChainMinCost_safety_wit_43
  proof_of_matrixChainMinCost_safety_wit_44 : matrixChainMinCost_safety_wit_44
  proof_of_matrixChainMinCost_safety_wit_45 : matrixChainMinCost_safety_wit_45
  proof_of_matrixChainMinCost_safety_wit_46 : matrixChainMinCost_safety_wit_46
  proof_of_matrixChainMinCost_safety_wit_47 : matrixChainMinCost_safety_wit_47
  proof_of_matrixChainMinCost_safety_wit_48 : matrixChainMinCost_safety_wit_48
  proof_of_matrixChainMinCost_entail_wit_4 : matrixChainMinCost_entail_wit_4
  proof_of_matrixChainMinCost_return_wit_1 : matrixChainMinCost_return_wit_1
  proof_of_matrixChainMinCost_partial_solve_wit_1 : matrixChainMinCost_partial_solve_wit_1
  proof_of_matrixChainMinCost_partial_solve_wit_2 : matrixChainMinCost_partial_solve_wit_2
  proof_of_matrixChainMinCost_partial_solve_wit_3 : matrixChainMinCost_partial_solve_wit_3
  proof_of_matrixChainMinCost_partial_solve_wit_4 : matrixChainMinCost_partial_solve_wit_4
  proof_of_matrixChainMinCost_partial_solve_wit_5 : matrixChainMinCost_partial_solve_wit_5
  proof_of_matrixChainMinCost_partial_solve_wit_6 : matrixChainMinCost_partial_solve_wit_6
  proof_of_matrixChainMinCost_partial_solve_wit_7 : matrixChainMinCost_partial_solve_wit_7
  proof_of_matrixChainMinCost_partial_solve_wit_8 : matrixChainMinCost_partial_solve_wit_8
  proof_of_matrixChainMinCost_partial_solve_wit_9 : matrixChainMinCost_partial_solve_wit_9
  proof_of_matrixChainMinCost_partial_solve_wit_10 : matrixChainMinCost_partial_solve_wit_10
  proof_of_matrixChainMinCost_partial_solve_wit_11 : matrixChainMinCost_partial_solve_wit_11
  proof_of_matrixChainMinCost_partial_solve_wit_12 : matrixChainMinCost_partial_solve_wit_12
  proof_of_matrixChainMinCost_partial_solve_wit_13 : matrixChainMinCost_partial_solve_wit_13
  proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1
  proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2
  proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3
  proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5
  proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6
  proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7
  proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8
  proof_of_matrixChainMinCost_entail_wit_9 : matrixChainMinCost_entail_wit_9
  proof_of_matrixChainMinCost_entail_wit_10_1 : matrixChainMinCost_entail_wit_10_1
  proof_of_matrixChainMinCost_entail_wit_10_2 : matrixChainMinCost_entail_wit_10_2
  proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11
  proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12
  proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13
  proof_of_matrixChainMinCost_entail_wit_14 : matrixChainMinCost_entail_wit_14

end Algorithms.matrix_chain_multiplication.lean.groundtruth.matrix_chain_multiplication_goal
