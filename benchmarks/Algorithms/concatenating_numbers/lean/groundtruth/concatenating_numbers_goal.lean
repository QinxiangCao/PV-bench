import SimpleC.SL.SeparationLogic

import Algorithms.concatenating_numbers.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.concatenating_numbers.lean.groundtruth.concatenating_numbers_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance concatenating_numbers_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def quicksort_numbers_safety_wit_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= count_pre)) (PreH7 : ((-1) <= high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH12 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : ((0 : Int) > low_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre <= count_pre)) (PreH8 : ((-1) <= high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH13 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ False ”

noncomputable def quicksort_numbers_safety_wit_3 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre >= count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ False ”

noncomputable def quicksort_numbers_safety_wit_4 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "boundary" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens)
  ** ((( &( "pivot_length" ) )) # Int |-> ((Znth high_pre lens (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
|--
  “ ((low_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (low_pre - 1)) ”

noncomputable def quicksort_numbers_safety_wit_5 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "boundary" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens)
  ** ((( &( "pivot_length" ) )) # Int |-> ((Znth high_pre lens (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_6 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ”
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ”
)

noncomputable def quicksort_numbers_safety_wit_6_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) <= INT_MAX) ”

noncomputable def quicksort_numbers_safety_wit_6_split_goal_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((INT_MIN) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ”

noncomputable def quicksort_numbers_safety_wit_7 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "comparison" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |-> (((Znth scan lens1 (0 : Int)) + pivot_length)))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_8 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |->_)
  ** ((( &( "comparison" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "total_length" ) )) # Int |-> (((Znth scan lens1 (0 : Int)) + pivot_length)))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_9 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + position))) (PreH2 : (((scan * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (current_length <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (comparison >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (current_length >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position < current_length)) (PreH24 : (position < total_length)) (PreH25 : (1 <= count_pre)) (PreH26 : (count_pre <= 20)) (PreH27 : (1 <= number_width_pre)) (PreH28 : (number_width_pre <= 10)) (PreH29 : ((0 : Int) <= low_pre)) (PreH30 : (low_pre < high_pre)) (PreH31 : (high_pre < count_pre)) (PreH32 : ((low_pre - 1) <= boundary)) (PreH33 : (boundary < scan)) (PreH34 : (low_pre <= scan)) (PreH35 : (scan < high_pre)) (PreH36 : (1 <= (sum (lens)))) (PreH37 : ((sum (lens)) <= 200)) (PreH38 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH39 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH40 : (1 <= current_length)) (PreH41 : (current_length <= number_width_pre)) (PreH42 : (1 <= pivot_length)) (PreH43 : (pivot_length <= number_width_pre)) (PreH44 : (total_length = (current_length + pivot_length))) (PreH45 : (comparison = (0 : Int))) (PreH46 : ((0 : Int) <= position)) (PreH47 : (position <= total_length)) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + position) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + position)) ”

noncomputable def quicksort_numbers_safety_wit_10 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + position))) (PreH2 : (((scan * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (current_length <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (comparison >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (current_length >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position < current_length)) (PreH24 : (position < total_length)) (PreH25 : (1 <= count_pre)) (PreH26 : (count_pre <= 20)) (PreH27 : (1 <= number_width_pre)) (PreH28 : (number_width_pre <= 10)) (PreH29 : ((0 : Int) <= low_pre)) (PreH30 : (low_pre < high_pre)) (PreH31 : (high_pre < count_pre)) (PreH32 : ((low_pre - 1) <= boundary)) (PreH33 : (boundary < scan)) (PreH34 : (low_pre <= scan)) (PreH35 : (scan < high_pre)) (PreH36 : (1 <= (sum (lens)))) (PreH37 : ((sum (lens)) <= 200)) (PreH38 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH39 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH40 : (1 <= current_length)) (PreH41 : (current_length <= number_width_pre)) (PreH42 : (1 <= pivot_length)) (PreH43 : (pivot_length <= number_width_pre)) (PreH44 : (total_length = (current_length + pivot_length))) (PreH45 : (comparison = (0 : Int))) (PreH46 : ((0 : Int) <= position)) (PreH47 : (position <= total_length)) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_11 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length)))) (PreH2 : (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - current_length))) (PreH4 : ((position - current_length) < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (scan <= INT_MAX)) (PreH9 : (boundary <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (count_pre <= INT_MAX)) (PreH13 : (comparison >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (pivot_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position >= current_length)) (PreH22 : (position < total_length)) (PreH23 : (1 <= count_pre)) (PreH24 : (count_pre <= 20)) (PreH25 : (1 <= number_width_pre)) (PreH26 : (number_width_pre <= 10)) (PreH27 : ((0 : Int) <= low_pre)) (PreH28 : (low_pre < high_pre)) (PreH29 : (high_pre < count_pre)) (PreH30 : ((low_pre - 1) <= boundary)) (PreH31 : (boundary < scan)) (PreH32 : (low_pre <= scan)) (PreH33 : (scan < high_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH37 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH38 : (1 <= current_length)) (PreH39 : (current_length <= number_width_pre)) (PreH40 : (1 <= pivot_length)) (PreH41 : (pivot_length <= number_width_pre)) (PreH42 : (total_length = (current_length + pivot_length))) (PreH43 : (comparison = (0 : Int))) (PreH44 : ((0 : Int) <= position)) (PreH45 : (position <= total_length)) (PreH46 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH49 : ((sum (lens1)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + (position - current_length)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + (position - current_length))) ”

noncomputable def quicksort_numbers_safety_wit_12 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length)))) (PreH2 : (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - current_length))) (PreH4 : ((position - current_length) < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (scan <= INT_MAX)) (PreH9 : (boundary <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (count_pre <= INT_MAX)) (PreH13 : (comparison >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (pivot_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position >= current_length)) (PreH22 : (position < total_length)) (PreH23 : (1 <= count_pre)) (PreH24 : (count_pre <= 20)) (PreH25 : (1 <= number_width_pre)) (PreH26 : (number_width_pre <= 10)) (PreH27 : ((0 : Int) <= low_pre)) (PreH28 : (low_pre < high_pre)) (PreH29 : (high_pre < count_pre)) (PreH30 : ((low_pre - 1) <= boundary)) (PreH31 : (boundary < scan)) (PreH32 : (low_pre <= scan)) (PreH33 : (scan < high_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH37 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH38 : (1 <= current_length)) (PreH39 : (current_length <= number_width_pre)) (PreH40 : (1 <= pivot_length)) (PreH41 : (pivot_length <= number_width_pre)) (PreH42 : (total_length = (current_length + pivot_length))) (PreH43 : (comparison = (0 : Int))) (PreH44 : ((0 : Int) <= position)) (PreH45 : (position <= total_length)) (PreH46 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH49 : ((sum (lens1)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((position - current_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (position - current_length)) ”

noncomputable def quicksort_numbers_safety_wit_13 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length)))) (PreH2 : (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - current_length))) (PreH4 : ((position - current_length) < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (scan <= INT_MAX)) (PreH9 : (boundary <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (count_pre <= INT_MAX)) (PreH13 : (comparison >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (pivot_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position >= current_length)) (PreH22 : (position < total_length)) (PreH23 : (1 <= count_pre)) (PreH24 : (count_pre <= 20)) (PreH25 : (1 <= number_width_pre)) (PreH26 : (number_width_pre <= 10)) (PreH27 : ((0 : Int) <= low_pre)) (PreH28 : (low_pre < high_pre)) (PreH29 : (high_pre < count_pre)) (PreH30 : ((low_pre - 1) <= boundary)) (PreH31 : (boundary < scan)) (PreH32 : (low_pre <= scan)) (PreH33 : (scan < high_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH37 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH38 : (1 <= current_length)) (PreH39 : (current_length <= number_width_pre)) (PreH40 : (1 <= pivot_length)) (PreH41 : (pivot_length <= number_width_pre)) (PreH42 : (total_length = (current_length + pivot_length))) (PreH43 : (comparison = (0 : Int))) (PreH44 : ((0 : Int) <= position)) (PreH45 : (position <= total_length)) (PreH46 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH49 : ((sum (lens1)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_14 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + position))) (PreH2 : (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (pivot_length <= INT_MAX)) (PreH10 : (scan <= INT_MAX)) (PreH11 : (boundary <= INT_MAX)) (PreH12 : (high_pre <= INT_MAX)) (PreH13 : (low_pre <= INT_MAX)) (PreH14 : (count_pre <= INT_MAX)) (PreH15 : (left_digit >= INT_MIN)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (total_length >= INT_MIN)) (PreH18 : (current_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position < pivot_length)) (PreH26 : (1 <= count_pre)) (PreH27 : (count_pre <= 20)) (PreH28 : (1 <= number_width_pre)) (PreH29 : (number_width_pre <= 10)) (PreH30 : ((0 : Int) <= low_pre)) (PreH31 : (low_pre < high_pre)) (PreH32 : (high_pre < count_pre)) (PreH33 : ((low_pre - 1) <= boundary)) (PreH34 : (boundary < scan)) (PreH35 : (low_pre <= scan)) (PreH36 : (scan < high_pre)) (PreH37 : (1 <= (sum (lens)))) (PreH38 : ((sum (lens)) <= 200)) (PreH39 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH40 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH41 : (1 <= current_length)) (PreH42 : (current_length <= number_width_pre)) (PreH43 : (1 <= pivot_length)) (PreH44 : (pivot_length <= number_width_pre)) (PreH45 : (total_length = (current_length + pivot_length))) (PreH46 : (comparison = (0 : Int))) (PreH47 : ((0 : Int) <= position)) (PreH48 : (position < total_length)) (PreH49 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH50 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH53 : ((sum (lens1)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + position) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + position)) ”

noncomputable def quicksort_numbers_safety_wit_15 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + position))) (PreH2 : (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (pivot_length <= INT_MAX)) (PreH10 : (scan <= INT_MAX)) (PreH11 : (boundary <= INT_MAX)) (PreH12 : (high_pre <= INT_MAX)) (PreH13 : (low_pre <= INT_MAX)) (PreH14 : (count_pre <= INT_MAX)) (PreH15 : (left_digit >= INT_MIN)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (total_length >= INT_MIN)) (PreH18 : (current_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position < pivot_length)) (PreH26 : (1 <= count_pre)) (PreH27 : (count_pre <= 20)) (PreH28 : (1 <= number_width_pre)) (PreH29 : (number_width_pre <= 10)) (PreH30 : ((0 : Int) <= low_pre)) (PreH31 : (low_pre < high_pre)) (PreH32 : (high_pre < count_pre)) (PreH33 : ((low_pre - 1) <= boundary)) (PreH34 : (boundary < scan)) (PreH35 : (low_pre <= scan)) (PreH36 : (scan < high_pre)) (PreH37 : (1 <= (sum (lens)))) (PreH38 : ((sum (lens)) <= 200)) (PreH39 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH40 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH41 : (1 <= current_length)) (PreH42 : (current_length <= number_width_pre)) (PreH43 : (1 <= pivot_length)) (PreH44 : (pivot_length <= number_width_pre)) (PreH45 : (total_length = (current_length + pivot_length))) (PreH46 : (comparison = (0 : Int))) (PreH47 : ((0 : Int) <= position)) (PreH48 : (position < total_length)) (PreH49 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH50 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH53 : ((sum (lens1)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_16 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length)))) (PreH2 : (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - pivot_length))) (PreH4 : ((position - pivot_length) < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (left_digit >= INT_MIN)) (PreH15 : (comparison >= INT_MIN)) (PreH16 : (total_length >= INT_MIN)) (PreH17 : (current_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position >= pivot_length)) (PreH24 : (1 <= count_pre)) (PreH25 : (count_pre <= 20)) (PreH26 : (1 <= number_width_pre)) (PreH27 : (number_width_pre <= 10)) (PreH28 : ((0 : Int) <= low_pre)) (PreH29 : (low_pre < high_pre)) (PreH30 : (high_pre < count_pre)) (PreH31 : ((low_pre - 1) <= boundary)) (PreH32 : (boundary < scan)) (PreH33 : (low_pre <= scan)) (PreH34 : (scan < high_pre)) (PreH35 : (1 <= (sum (lens)))) (PreH36 : ((sum (lens)) <= 200)) (PreH37 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH38 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH39 : (1 <= current_length)) (PreH40 : (current_length <= number_width_pre)) (PreH41 : (1 <= pivot_length)) (PreH42 : (pivot_length <= number_width_pre)) (PreH43 : (total_length = (current_length + pivot_length))) (PreH44 : (comparison = (0 : Int))) (PreH45 : ((0 : Int) <= position)) (PreH46 : (position < total_length)) (PreH47 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + (position - pivot_length)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + (position - pivot_length))) ”

noncomputable def quicksort_numbers_safety_wit_17 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length)))) (PreH2 : (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - pivot_length))) (PreH4 : ((position - pivot_length) < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (left_digit >= INT_MIN)) (PreH15 : (comparison >= INT_MIN)) (PreH16 : (total_length >= INT_MIN)) (PreH17 : (current_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position >= pivot_length)) (PreH24 : (1 <= count_pre)) (PreH25 : (count_pre <= 20)) (PreH26 : (1 <= number_width_pre)) (PreH27 : (number_width_pre <= 10)) (PreH28 : ((0 : Int) <= low_pre)) (PreH29 : (low_pre < high_pre)) (PreH30 : (high_pre < count_pre)) (PreH31 : ((low_pre - 1) <= boundary)) (PreH32 : (boundary < scan)) (PreH33 : (low_pre <= scan)) (PreH34 : (scan < high_pre)) (PreH35 : (1 <= (sum (lens)))) (PreH36 : ((sum (lens)) <= 200)) (PreH37 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH38 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH39 : (1 <= current_length)) (PreH40 : (current_length <= number_width_pre)) (PreH41 : (1 <= pivot_length)) (PreH42 : (pivot_length <= number_width_pre)) (PreH43 : (total_length = (current_length + pivot_length))) (PreH44 : (comparison = (0 : Int))) (PreH45 : ((0 : Int) <= position)) (PreH46 : (position < total_length)) (PreH47 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((position - pivot_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (position - pivot_length)) ”

noncomputable def quicksort_numbers_safety_wit_18 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length)))) (PreH2 : (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - pivot_length))) (PreH4 : ((position - pivot_length) < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (left_digit >= INT_MIN)) (PreH15 : (comparison >= INT_MIN)) (PreH16 : (total_length >= INT_MIN)) (PreH17 : (current_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position >= pivot_length)) (PreH24 : (1 <= count_pre)) (PreH25 : (count_pre <= 20)) (PreH26 : (1 <= number_width_pre)) (PreH27 : (number_width_pre <= 10)) (PreH28 : ((0 : Int) <= low_pre)) (PreH29 : (low_pre < high_pre)) (PreH30 : (high_pre < count_pre)) (PreH31 : ((low_pre - 1) <= boundary)) (PreH32 : (boundary < scan)) (PreH33 : (low_pre <= scan)) (PreH34 : (scan < high_pre)) (PreH35 : (1 <= (sum (lens)))) (PreH36 : ((sum (lens)) <= 200)) (PreH37 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH38 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH39 : (1 <= current_length)) (PreH40 : (current_length <= number_width_pre)) (PreH41 : (1 <= pivot_length)) (PreH42 : (pivot_length <= number_width_pre)) (PreH43 : (total_length = (current_length + pivot_length))) (PreH44 : (comparison = (0 : Int))) (PreH45 : ((0 : Int) <= position)) (PreH46 : (position < total_length)) (PreH47 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_19 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((left_digit - right_digit) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_digit - right_digit)) ”
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((left_digit - right_digit) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_digit - right_digit)) ”
)

noncomputable def quicksort_numbers_safety_wit_19_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((left_digit - right_digit) <= INT_MAX) ”

noncomputable def quicksort_numbers_safety_wit_19_split_goal_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((INT_MIN) <= (left_digit - right_digit)) ”

noncomputable def quicksort_numbers_safety_wit_20 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit = right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((position + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (position + 1)) ”

noncomputable def quicksort_numbers_safety_wit_21 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre < high_pre)) (PreH7 : (high_pre < count_pre)) (PreH8 : ((low_pre - 1) <= boundary)) (PreH9 : (boundary < scan)) (PreH10 : (low_pre <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH15 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH16 : (1 <= current_length)) (PreH17 : (current_length <= number_width_pre)) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : (total_length = (current_length + pivot_length))) (PreH21 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH22 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH23 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_22 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH23 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH24 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison)) (PreH25 : ((sum (lens1)) = (sum (lens)))) (PreH26 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "column" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary + 1)) ”

noncomputable def quicksort_numbers_safety_wit_23 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH23 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH24 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison)) (PreH25 : ((sum (lens1)) = (sum (lens)))) (PreH26 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "column" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> ((boundary + 1)))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_24 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((boundary * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((boundary * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_25 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_26 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((boundary * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((boundary * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_27 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_28 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_29 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_30 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_31 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_32 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((scan * number_width_pre) + column)) ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))) ((replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((column + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (column + 1)) ”

noncomputable def quicksort_numbers_safety_wit_33 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre < high_pre)) (PreH7 : (high_pre < count_pre)) (PreH8 : ((low_pre - 1) <= boundary)) (PreH9 : (boundary <= scan)) (PreH10 : (scan < high_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH14 : (1 <= pivot_length)) (PreH15 : (pivot_length <= number_width_pre)) (PreH16 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH17 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1))) (PreH18 : ((sum (lens1)) = (sum (lens)))) (PreH19 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan + 1)) ”

noncomputable def quicksort_numbers_safety_wit_34 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary + 1)) ”

noncomputable def quicksort_numbers_safety_wit_35 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_36 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "column" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |-> ((boundary + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_37 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((pivot * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((pivot * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_38 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((pivot * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_39 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((pivot * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((pivot * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_40 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((pivot * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_41 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_42 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_43 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_44 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_45 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((high_pre * number_width_pre) + column)) ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))) ((replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((column + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (column + 1)) ”

noncomputable def quicksort_numbers_safety_wit_46 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH14 : (PairedPermutation rows rows1 lens lens1)) (PreH15 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH16 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH17 : ((sum (lens1)) = (sum (lens)))) (PreH18 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((pivot - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot - 1)) ”

noncomputable def quicksort_numbers_safety_wit_47 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH14 : (PairedPermutation rows rows1 lens lens1)) (PreH15 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH16 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH17 : ((sum (lens1)) = (sum (lens)))) (PreH18 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_48 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH3 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH4 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH5 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH7 : ((sum (lens2)) = (sum (lens1)))) (PreH8 : (pivot > low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1 lens lens1)) (PreH22 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((pivot + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot + 1)) ”

noncomputable def quicksort_numbers_safety_wit_49 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH3 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH4 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH5 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH7 : ((sum (lens2)) = (sum (lens1)))) (PreH8 : (pivot > low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1 lens lens1)) (PreH22 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_50 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot >= high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (low_pre <= pivot)) (PreH11 : (pivot <= high_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1 lens lens1)) (PreH16 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH17 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH18 : ((sum (lens1)) = (sum (lens)))) (PreH19 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ False ”

noncomputable def quicksort_numbers_safety_wit_51 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (low_pre <= pivot)) (PreH11 : (pivot <= high_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1 lens lens1)) (PreH16 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH17 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH18 : ((sum (lens1)) = (sum (lens)))) (PreH19 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((pivot + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot + 1)) ”

noncomputable def quicksort_numbers_safety_wit_52 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (low_pre <= pivot)) (PreH11 : (pivot <= high_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1 lens lens1)) (PreH16 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH17 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH18 : ((sum (lens1)) = (sum (lens)))) (PreH19 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_entail_wit_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (low_pre <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Znth high_pre lens (0 : Int)) = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth high_pre lens (0 : Int))) ” &&
  “ ((Znth high_pre lens (0 : Int)) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre (low_pre - 1) low_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= low_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (low_pre <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ ((Znth high_pre lens (0 : Int)) = (Znth (high_pre) (lens) ((0 : Int)))) ” &&
  “ (1 <= (Znth high_pre lens (0 : Int))) ” &&
  “ ((Znth high_pre lens (0 : Int)) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens low_pre high_pre (low_pre - 1) low_pre) ” &&
  “ (FlatRows flat rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1_2 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1_2 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1_2 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int)))) ” &&
  “ ((Znth scan lens1 (0 : Int)) = (Znth (scan) (lens1_2) ((0 : Int)))) ” &&
  “ (1 <= (Znth scan lens1 (0 : Int))) ” &&
  “ ((Znth scan lens1 (0 : Int)) <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) = ((Znth scan lens1 (0 : Int)) + pivot_length)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre (0 : Int)) ” &&
  “ ((sum (lens1_2)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1_2 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1_2 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((Znth scan lens1 (0 : Int)) = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth scan lens1 (0 : Int))) ” &&
  “ ((Znth scan lens1 (0 : Int)) <= number_width_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((Znth scan lens1 (0 : Int)) + (Znth (high_pre) (lens1) ((0 : Int))))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre (0 : Int)) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_3 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1) <= boundary)) (PreH11 : (boundary < scan)) (PreH12 : (low_pre <= scan)) (PreH13 : (scan < high_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH17 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH18 : (1 <= current_length)) (PreH19 : (current_length <= number_width_pre)) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : (total_length = (current_length + pivot_length))) (PreH23 : (comparison = (0 : Int))) (PreH24 : ((0 : Int) <= position)) (PreH25 : (position <= total_length)) (PreH26 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH27 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH28 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= position) ” &&
  “ (position < number_width_pre) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position < current_length) ” &&
  “ (position < total_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)

noncomputable def quicksort_numbers_entail_wit_4 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= position)) (PreH2 : (position < number_width_pre)) (PreH3 : (comparison <= INT_MAX)) (PreH4 : (total_length <= INT_MAX)) (PreH5 : (current_length <= INT_MAX)) (PreH6 : (pivot_length <= INT_MAX)) (PreH7 : (scan <= INT_MAX)) (PreH8 : (boundary <= INT_MAX)) (PreH9 : (high_pre <= INT_MAX)) (PreH10 : (low_pre <= INT_MAX)) (PreH11 : (count_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (total_length >= INT_MIN)) (PreH14 : (current_length >= INT_MIN)) (PreH15 : (pivot_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position < current_length)) (PreH22 : (position < total_length)) (PreH23 : (1 <= count_pre)) (PreH24 : (count_pre <= 20)) (PreH25 : (1 <= number_width_pre)) (PreH26 : (number_width_pre <= 10)) (PreH27 : ((0 : Int) <= low_pre)) (PreH28 : (low_pre < high_pre)) (PreH29 : (high_pre < count_pre)) (PreH30 : ((low_pre - 1) <= boundary)) (PreH31 : (boundary < scan)) (PreH32 : (low_pre <= scan)) (PreH33 : (scan < high_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH37 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH38 : (1 <= current_length)) (PreH39 : (current_length <= number_width_pre)) (PreH40 : (1 <= pivot_length)) (PreH41 : (pivot_length <= number_width_pre)) (PreH42 : (total_length = (current_length + pivot_length))) (PreH43 : (comparison = (0 : Int))) (PreH44 : ((0 : Int) <= position)) (PreH45 : (position <= total_length)) (PreH46 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH49 : ((sum (lens1)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + position)) ” &&
  “ (((scan * number_width_pre) + position) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < number_width_pre) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position < current_length) ” &&
  “ (position < total_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : ((0 : Int) <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (total_length <= INT_MAX)) (PreH9 : (current_length <= INT_MAX)) (PreH10 : (pivot_length <= INT_MAX)) (PreH11 : (scan <= INT_MAX)) (PreH12 : (boundary <= INT_MAX)) (PreH13 : (high_pre <= INT_MAX)) (PreH14 : (low_pre <= INT_MAX)) (PreH15 : (count_pre <= INT_MAX)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (total_length >= INT_MIN)) (PreH18 : (current_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position < current_length)) (PreH26 : (position < total_length)) (PreH27 : (1 <= count_pre)) (PreH28 : (count_pre <= 20)) (PreH29 : (1 <= number_width_pre)) (PreH30 : (number_width_pre <= 10)) (PreH31 : ((0 : Int) <= low_pre)) (PreH32 : (low_pre < high_pre)) (PreH33 : (high_pre < count_pre)) (PreH34 : ((low_pre - 1) <= boundary)) (PreH35 : (boundary < scan)) (PreH36 : (low_pre <= scan)) (PreH37 : (scan < high_pre)) (PreH38 : (1 <= (sum (lens)))) (PreH39 : ((sum (lens)) <= 200)) (PreH40 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH41 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH42 : (1 <= current_length)) (PreH43 : (current_length <= number_width_pre)) (PreH44 : (1 <= pivot_length)) (PreH45 : (pivot_length <= number_width_pre)) (PreH46 : (total_length = (current_length + pivot_length))) (PreH47 : (comparison = (0 : Int))) (PreH48 : ((0 : Int) <= position)) (PreH49 : (position <= total_length)) (PreH50 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH53 : ((sum (lens1)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((scan * number_width_pre) + position) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_4_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : ((0 : Int) <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (total_length <= INT_MAX)) (PreH9 : (current_length <= INT_MAX)) (PreH10 : (pivot_length <= INT_MAX)) (PreH11 : (scan <= INT_MAX)) (PreH12 : (boundary <= INT_MAX)) (PreH13 : (high_pre <= INT_MAX)) (PreH14 : (low_pre <= INT_MAX)) (PreH15 : (count_pre <= INT_MAX)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (total_length >= INT_MIN)) (PreH18 : (current_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position < current_length)) (PreH26 : (position < total_length)) (PreH27 : (1 <= count_pre)) (PreH28 : (count_pre <= 20)) (PreH29 : (1 <= number_width_pre)) (PreH30 : (number_width_pre <= 10)) (PreH31 : ((0 : Int) <= low_pre)) (PreH32 : (low_pre < high_pre)) (PreH33 : (high_pre < count_pre)) (PreH34 : ((low_pre - 1) <= boundary)) (PreH35 : (boundary < scan)) (PreH36 : (low_pre <= scan)) (PreH37 : (scan < high_pre)) (PreH38 : (1 <= (sum (lens)))) (PreH39 : ((sum (lens)) <= 200)) (PreH40 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH41 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH42 : (1 <= current_length)) (PreH43 : (current_length <= number_width_pre)) (PreH44 : (1 <= pivot_length)) (PreH45 : (pivot_length <= number_width_pre)) (PreH46 : (total_length = (current_length + pivot_length))) (PreH47 : (comparison = (0 : Int))) (PreH48 : ((0 : Int) <= position)) (PreH49 : (position <= total_length)) (PreH50 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH53 : ((sum (lens1)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (((scan * number_width_pre) + position) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_5 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1) <= boundary)) (PreH11 : (boundary < scan)) (PreH12 : (low_pre <= scan)) (PreH13 : (scan < high_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH17 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH18 : (1 <= current_length)) (PreH19 : (current_length <= number_width_pre)) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : (total_length = (current_length + pivot_length))) (PreH23 : (comparison = (0 : Int))) (PreH24 : ((0 : Int) <= position)) (PreH25 : (position <= total_length)) (PreH26 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH27 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH28 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= (position - current_length)) ” &&
  “ ((position - current_length) < number_width_pre) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position >= current_length) ” &&
  “ (position < total_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)

noncomputable def quicksort_numbers_entail_wit_6 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= (position - current_length))) (PreH2 : ((position - current_length) < number_width_pre)) (PreH3 : (comparison <= INT_MAX)) (PreH4 : (total_length <= INT_MAX)) (PreH5 : (pivot_length <= INT_MAX)) (PreH6 : (scan <= INT_MAX)) (PreH7 : (boundary <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (count_pre <= INT_MAX)) (PreH11 : (comparison >= INT_MIN)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (boundary >= INT_MIN)) (PreH16 : (high_pre >= INT_MIN)) (PreH17 : (low_pre >= INT_MIN)) (PreH18 : (count_pre >= INT_MIN)) (PreH19 : (position >= current_length)) (PreH20 : (position < total_length)) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : ((low_pre - 1) <= boundary)) (PreH29 : (boundary < scan)) (PreH30 : (low_pre <= scan)) (PreH31 : (scan < high_pre)) (PreH32 : (1 <= (sum (lens)))) (PreH33 : ((sum (lens)) <= 200)) (PreH34 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH35 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH36 : (1 <= current_length)) (PreH37 : (current_length <= number_width_pre)) (PreH38 : (1 <= pivot_length)) (PreH39 : (pivot_length <= number_width_pre)) (PreH40 : (total_length = (current_length + pivot_length))) (PreH41 : (comparison = (0 : Int))) (PreH42 : ((0 : Int) <= position)) (PreH43 : (position <= total_length)) (PreH44 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH45 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH46 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH47 : ((sum (lens1)) = (sum (lens)))) (PreH48 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length))) ” &&
  “ (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (position - current_length)) ” &&
  “ ((position - current_length) < number_width_pre) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position >= current_length) ” &&
  “ (position < total_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (current_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (current_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : ((0 : Int) <= (position - current_length))) (PreH8 : ((position - current_length) < number_width_pre)) (PreH9 : (comparison <= INT_MAX)) (PreH10 : (total_length <= INT_MAX)) (PreH11 : (pivot_length <= INT_MAX)) (PreH12 : (scan <= INT_MAX)) (PreH13 : (boundary <= INT_MAX)) (PreH14 : (high_pre <= INT_MAX)) (PreH15 : (low_pre <= INT_MAX)) (PreH16 : (count_pre <= INT_MAX)) (PreH17 : (comparison >= INT_MIN)) (PreH18 : (total_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position >= current_length)) (PreH26 : (position < total_length)) (PreH27 : (1 <= count_pre)) (PreH28 : (count_pre <= 20)) (PreH29 : (1 <= number_width_pre)) (PreH30 : (number_width_pre <= 10)) (PreH31 : ((0 : Int) <= low_pre)) (PreH32 : (low_pre < high_pre)) (PreH33 : (high_pre < count_pre)) (PreH34 : ((low_pre - 1) <= boundary)) (PreH35 : (boundary < scan)) (PreH36 : (low_pre <= scan)) (PreH37 : (scan < high_pre)) (PreH38 : (1 <= (sum (lens)))) (PreH39 : ((sum (lens)) <= 200)) (PreH40 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH41 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH42 : (1 <= current_length)) (PreH43 : (current_length <= number_width_pre)) (PreH44 : (1 <= pivot_length)) (PreH45 : (pivot_length <= number_width_pre)) (PreH46 : (total_length = (current_length + pivot_length))) (PreH47 : (comparison = (0 : Int))) (PreH48 : ((0 : Int) <= position)) (PreH49 : (position <= total_length)) (PreH50 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH53 : ((sum (lens1)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_6_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (current_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (current_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : ((0 : Int) <= (position - current_length))) (PreH8 : ((position - current_length) < number_width_pre)) (PreH9 : (comparison <= INT_MAX)) (PreH10 : (total_length <= INT_MAX)) (PreH11 : (pivot_length <= INT_MAX)) (PreH12 : (scan <= INT_MAX)) (PreH13 : (boundary <= INT_MAX)) (PreH14 : (high_pre <= INT_MAX)) (PreH15 : (low_pre <= INT_MAX)) (PreH16 : (count_pre <= INT_MAX)) (PreH17 : (comparison >= INT_MIN)) (PreH18 : (total_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position >= current_length)) (PreH26 : (position < total_length)) (PreH27 : (1 <= count_pre)) (PreH28 : (count_pre <= 20)) (PreH29 : (1 <= number_width_pre)) (PreH30 : (number_width_pre <= 10)) (PreH31 : ((0 : Int) <= low_pre)) (PreH32 : (low_pre < high_pre)) (PreH33 : (high_pre < count_pre)) (PreH34 : ((low_pre - 1) <= boundary)) (PreH35 : (boundary < scan)) (PreH36 : (low_pre <= scan)) (PreH37 : (scan < high_pre)) (PreH38 : (1 <= (sum (lens)))) (PreH39 : ((sum (lens)) <= 200)) (PreH40 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH41 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH42 : (1 <= current_length)) (PreH43 : (current_length <= number_width_pre)) (PreH44 : (1 <= pivot_length)) (PreH45 : (pivot_length <= number_width_pre)) (PreH46 : (total_length = (current_length + pivot_length))) (PreH47 : (comparison = (0 : Int))) (PreH48 : ((0 : Int) <= position)) (PreH49 : (position <= total_length)) (PreH50 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH53 : ((sum (lens1)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_7_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + position))) (PreH2 : (((scan * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (current_length <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (comparison >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (current_length >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position < current_length)) (PreH24 : (position < total_length)) (PreH25 : (1 <= count_pre)) (PreH26 : (count_pre <= 20)) (PreH27 : (1 <= number_width_pre)) (PreH28 : (number_width_pre <= 10)) (PreH29 : ((0 : Int) <= low_pre)) (PreH30 : (low_pre < high_pre)) (PreH31 : (high_pre < count_pre)) (PreH32 : ((low_pre - 1) <= boundary)) (PreH33 : (boundary < scan)) (PreH34 : (low_pre <= scan)) (PreH35 : (scan < high_pre)) (PreH36 : (1 <= (sum (lens)))) (PreH37 : ((sum (lens)) <= 200)) (PreH38 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH39 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH40 : (1 <= current_length)) (PreH41 : (current_length <= number_width_pre)) (PreH42 : (1 <= pivot_length)) (PreH43 : (pivot_length <= number_width_pre)) (PreH44 : (total_length = (current_length + pivot_length))) (PreH45 : (comparison = (0 : Int))) (PreH46 : ((0 : Int) <= position)) (PreH47 : (position <= total_length)) (PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH51 : ((sum (lens1_2)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ ((Znth ((scan * number_width_pre) + position) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + position))) (PreH2 : (((scan * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (current_length <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (comparison >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (current_length >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position < current_length)) (PreH24 : (position < total_length)) (PreH25 : (1 <= count_pre)) (PreH26 : (count_pre <= 20)) (PreH27 : (1 <= number_width_pre)) (PreH28 : (number_width_pre <= 10)) (PreH29 : ((0 : Int) <= low_pre)) (PreH30 : (low_pre < high_pre)) (PreH31 : (high_pre < count_pre)) (PreH32 : ((low_pre - 1) <= boundary)) (PreH33 : (boundary < scan)) (PreH34 : (low_pre <= scan)) (PreH35 : (scan < high_pre)) (PreH36 : (1 <= (sum (lens)))) (PreH37 : ((sum (lens)) <= 200)) (PreH38 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH39 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH40 : (1 <= current_length)) (PreH41 : (current_length <= number_width_pre)) (PreH42 : (1 <= pivot_length)) (PreH43 : (pivot_length <= number_width_pre)) (PreH44 : (total_length = (current_length + pivot_length))) (PreH45 : (comparison = (0 : Int))) (PreH46 : ((0 : Int) <= position)) (PreH47 : (position <= total_length)) (PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH51 : ((sum (lens1_2)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= position) ” &&
  “ ((Znth ((scan * number_width_pre) + position) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_7_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length)))) (PreH2 : (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - current_length))) (PreH4 : ((position - current_length) < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (scan <= INT_MAX)) (PreH9 : (boundary <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (count_pre <= INT_MAX)) (PreH13 : (comparison >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (pivot_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position >= current_length)) (PreH22 : (position < total_length)) (PreH23 : (1 <= count_pre)) (PreH24 : (count_pre <= 20)) (PreH25 : (1 <= number_width_pre)) (PreH26 : (number_width_pre <= 10)) (PreH27 : ((0 : Int) <= low_pre)) (PreH28 : (low_pre < high_pre)) (PreH29 : (high_pre < count_pre)) (PreH30 : ((low_pre - 1) <= boundary)) (PreH31 : (boundary < scan)) (PreH32 : (low_pre <= scan)) (PreH33 : (scan < high_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH37 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH38 : (1 <= current_length)) (PreH39 : (current_length <= number_width_pre)) (PreH40 : (1 <= pivot_length)) (PreH41 : (pivot_length <= number_width_pre)) (PreH42 : (total_length = (current_length + pivot_length))) (PreH43 : (comparison = (0 : Int))) (PreH44 : ((0 : Int) <= position)) (PreH45 : (position <= total_length)) (PreH46 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH49 : ((sum (lens1_2)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ ((Znth ((high_pre * number_width_pre) + (position - current_length)) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length)))) (PreH2 : (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - current_length))) (PreH4 : ((position - current_length) < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (scan <= INT_MAX)) (PreH9 : (boundary <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (count_pre <= INT_MAX)) (PreH13 : (comparison >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (pivot_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position >= current_length)) (PreH22 : (position < total_length)) (PreH23 : (1 <= count_pre)) (PreH24 : (count_pre <= 20)) (PreH25 : (1 <= number_width_pre)) (PreH26 : (number_width_pre <= 10)) (PreH27 : ((0 : Int) <= low_pre)) (PreH28 : (low_pre < high_pre)) (PreH29 : (high_pre < count_pre)) (PreH30 : ((low_pre - 1) <= boundary)) (PreH31 : (boundary < scan)) (PreH32 : (low_pre <= scan)) (PreH33 : (scan < high_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH37 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH38 : (1 <= current_length)) (PreH39 : (current_length <= number_width_pre)) (PreH40 : (1 <= pivot_length)) (PreH41 : (pivot_length <= number_width_pre)) (PreH42 : (total_length = (current_length + pivot_length))) (PreH43 : (comparison = (0 : Int))) (PreH44 : ((0 : Int) <= position)) (PreH45 : (position <= total_length)) (PreH46 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH49 : ((sum (lens1_2)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((Znth ((high_pre * number_width_pre) + (position - (Znth (scan) (lens1_2) ((0 : Int))))) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_8 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position < pivot_length)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH26 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH27 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH28 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= position) ” &&
  “ (position < number_width_pre) ” &&
  “ (left_digit <= INT_MAX) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (left_digit >= INT_MIN) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position < pivot_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)

noncomputable def quicksort_numbers_entail_wit_9 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= position)) (PreH2 : (position < number_width_pre)) (PreH3 : (left_digit <= INT_MAX)) (PreH4 : (comparison <= INT_MAX)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (current_length <= INT_MAX)) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (scan <= INT_MAX)) (PreH9 : (boundary <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (count_pre <= INT_MAX)) (PreH13 : (left_digit >= INT_MIN)) (PreH14 : (comparison >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (current_length >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position < pivot_length)) (PreH24 : (1 <= count_pre)) (PreH25 : (count_pre <= 20)) (PreH26 : (1 <= number_width_pre)) (PreH27 : (number_width_pre <= 10)) (PreH28 : ((0 : Int) <= low_pre)) (PreH29 : (low_pre < high_pre)) (PreH30 : (high_pre < count_pre)) (PreH31 : ((low_pre - 1) <= boundary)) (PreH32 : (boundary < scan)) (PreH33 : (low_pre <= scan)) (PreH34 : (scan < high_pre)) (PreH35 : (1 <= (sum (lens)))) (PreH36 : ((sum (lens)) <= 200)) (PreH37 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH38 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH39 : (1 <= current_length)) (PreH40 : (current_length <= number_width_pre)) (PreH41 : (1 <= pivot_length)) (PreH42 : (pivot_length <= number_width_pre)) (PreH43 : (total_length = (current_length + pivot_length))) (PreH44 : (comparison = (0 : Int))) (PreH45 : ((0 : Int) <= position)) (PreH46 : (position < total_length)) (PreH47 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + position)) ” &&
  “ (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < number_width_pre) ” &&
  “ (left_digit <= INT_MAX) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (left_digit >= INT_MIN) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position < pivot_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : ((0 : Int) <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (left_digit <= INT_MAX)) (PreH8 : (comparison <= INT_MAX)) (PreH9 : (total_length <= INT_MAX)) (PreH10 : (current_length <= INT_MAX)) (PreH11 : (pivot_length <= INT_MAX)) (PreH12 : (scan <= INT_MAX)) (PreH13 : (boundary <= INT_MAX)) (PreH14 : (high_pre <= INT_MAX)) (PreH15 : (low_pre <= INT_MAX)) (PreH16 : (count_pre <= INT_MAX)) (PreH17 : (left_digit >= INT_MIN)) (PreH18 : (comparison >= INT_MIN)) (PreH19 : (total_length >= INT_MIN)) (PreH20 : (current_length >= INT_MIN)) (PreH21 : (pivot_length >= INT_MIN)) (PreH22 : (scan >= INT_MIN)) (PreH23 : (boundary >= INT_MIN)) (PreH24 : (high_pre >= INT_MIN)) (PreH25 : (low_pre >= INT_MIN)) (PreH26 : (count_pre >= INT_MIN)) (PreH27 : (position < pivot_length)) (PreH28 : (1 <= count_pre)) (PreH29 : (count_pre <= 20)) (PreH30 : (1 <= number_width_pre)) (PreH31 : (number_width_pre <= 10)) (PreH32 : ((0 : Int) <= low_pre)) (PreH33 : (low_pre < high_pre)) (PreH34 : (high_pre < count_pre)) (PreH35 : ((low_pre - 1) <= boundary)) (PreH36 : (boundary < scan)) (PreH37 : (low_pre <= scan)) (PreH38 : (scan < high_pre)) (PreH39 : (1 <= (sum (lens)))) (PreH40 : ((sum (lens)) <= 200)) (PreH41 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH42 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH43 : (1 <= current_length)) (PreH44 : (current_length <= number_width_pre)) (PreH45 : (1 <= pivot_length)) (PreH46 : (pivot_length <= number_width_pre)) (PreH47 : (total_length = (current_length + pivot_length))) (PreH48 : (comparison = (0 : Int))) (PreH49 : ((0 : Int) <= position)) (PreH50 : (position < total_length)) (PreH51 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH52 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH53 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH54 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH55 : ((sum (lens1)) = (sum (lens)))) (PreH56 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_9_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : ((0 : Int) <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (left_digit <= INT_MAX)) (PreH8 : (comparison <= INT_MAX)) (PreH9 : (total_length <= INT_MAX)) (PreH10 : (current_length <= INT_MAX)) (PreH11 : (pivot_length <= INT_MAX)) (PreH12 : (scan <= INT_MAX)) (PreH13 : (boundary <= INT_MAX)) (PreH14 : (high_pre <= INT_MAX)) (PreH15 : (low_pre <= INT_MAX)) (PreH16 : (count_pre <= INT_MAX)) (PreH17 : (left_digit >= INT_MIN)) (PreH18 : (comparison >= INT_MIN)) (PreH19 : (total_length >= INT_MIN)) (PreH20 : (current_length >= INT_MIN)) (PreH21 : (pivot_length >= INT_MIN)) (PreH22 : (scan >= INT_MIN)) (PreH23 : (boundary >= INT_MIN)) (PreH24 : (high_pre >= INT_MIN)) (PreH25 : (low_pre >= INT_MIN)) (PreH26 : (count_pre >= INT_MIN)) (PreH27 : (position < pivot_length)) (PreH28 : (1 <= count_pre)) (PreH29 : (count_pre <= 20)) (PreH30 : (1 <= number_width_pre)) (PreH31 : (number_width_pre <= 10)) (PreH32 : ((0 : Int) <= low_pre)) (PreH33 : (low_pre < high_pre)) (PreH34 : (high_pre < count_pre)) (PreH35 : ((low_pre - 1) <= boundary)) (PreH36 : (boundary < scan)) (PreH37 : (low_pre <= scan)) (PreH38 : (scan < high_pre)) (PreH39 : (1 <= (sum (lens)))) (PreH40 : ((sum (lens)) <= 200)) (PreH41 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH42 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH43 : (1 <= current_length)) (PreH44 : (current_length <= number_width_pre)) (PreH45 : (1 <= pivot_length)) (PreH46 : (pivot_length <= number_width_pre)) (PreH47 : (total_length = (current_length + pivot_length))) (PreH48 : (comparison = (0 : Int))) (PreH49 : ((0 : Int) <= position)) (PreH50 : (position < total_length)) (PreH51 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH52 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH53 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH54 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH55 : ((sum (lens1)) = (sum (lens)))) (PreH56 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_10 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position >= pivot_length)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH26 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH27 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH28 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= (position - pivot_length)) ” &&
  “ ((position - pivot_length) < number_width_pre) ” &&
  “ (left_digit <= INT_MAX) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (left_digit >= INT_MIN) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position >= pivot_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)

noncomputable def quicksort_numbers_entail_wit_11 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= (position - pivot_length))) (PreH2 : ((position - pivot_length) < number_width_pre)) (PreH3 : (left_digit <= INT_MAX)) (PreH4 : (comparison <= INT_MAX)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (current_length <= INT_MAX)) (PreH7 : (scan <= INT_MAX)) (PreH8 : (boundary <= INT_MAX)) (PreH9 : (high_pre <= INT_MAX)) (PreH10 : (low_pre <= INT_MAX)) (PreH11 : (count_pre <= INT_MAX)) (PreH12 : (left_digit >= INT_MIN)) (PreH13 : (comparison >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (current_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position >= pivot_length)) (PreH22 : (1 <= count_pre)) (PreH23 : (count_pre <= 20)) (PreH24 : (1 <= number_width_pre)) (PreH25 : (number_width_pre <= 10)) (PreH26 : ((0 : Int) <= low_pre)) (PreH27 : (low_pre < high_pre)) (PreH28 : (high_pre < count_pre)) (PreH29 : ((low_pre - 1) <= boundary)) (PreH30 : (boundary < scan)) (PreH31 : (low_pre <= scan)) (PreH32 : (scan < high_pre)) (PreH33 : (1 <= (sum (lens)))) (PreH34 : ((sum (lens)) <= 200)) (PreH35 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH36 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH37 : (1 <= current_length)) (PreH38 : (current_length <= number_width_pre)) (PreH39 : (1 <= pivot_length)) (PreH40 : (pivot_length <= number_width_pre)) (PreH41 : (total_length = (current_length + pivot_length))) (PreH42 : (comparison = (0 : Int))) (PreH43 : ((0 : Int) <= position)) (PreH44 : (position < total_length)) (PreH45 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH46 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH49 : ((sum (lens1)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length))) ” &&
  “ (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (position - pivot_length)) ” &&
  “ ((position - pivot_length) < number_width_pre) ” &&
  “ (left_digit <= INT_MAX) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (left_digit >= INT_MIN) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position >= pivot_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (pivot_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (pivot_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : ((0 : Int) <= (position - pivot_length))) (PreH8 : ((position - pivot_length) < number_width_pre)) (PreH9 : (left_digit <= INT_MAX)) (PreH10 : (comparison <= INT_MAX)) (PreH11 : (total_length <= INT_MAX)) (PreH12 : (current_length <= INT_MAX)) (PreH13 : (scan <= INT_MAX)) (PreH14 : (boundary <= INT_MAX)) (PreH15 : (high_pre <= INT_MAX)) (PreH16 : (low_pre <= INT_MAX)) (PreH17 : (count_pre <= INT_MAX)) (PreH18 : (left_digit >= INT_MIN)) (PreH19 : (comparison >= INT_MIN)) (PreH20 : (total_length >= INT_MIN)) (PreH21 : (current_length >= INT_MIN)) (PreH22 : (scan >= INT_MIN)) (PreH23 : (boundary >= INT_MIN)) (PreH24 : (high_pre >= INT_MIN)) (PreH25 : (low_pre >= INT_MIN)) (PreH26 : (count_pre >= INT_MIN)) (PreH27 : (position >= pivot_length)) (PreH28 : (1 <= count_pre)) (PreH29 : (count_pre <= 20)) (PreH30 : (1 <= number_width_pre)) (PreH31 : (number_width_pre <= 10)) (PreH32 : ((0 : Int) <= low_pre)) (PreH33 : (low_pre < high_pre)) (PreH34 : (high_pre < count_pre)) (PreH35 : ((low_pre - 1) <= boundary)) (PreH36 : (boundary < scan)) (PreH37 : (low_pre <= scan)) (PreH38 : (scan < high_pre)) (PreH39 : (1 <= (sum (lens)))) (PreH40 : ((sum (lens)) <= 200)) (PreH41 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH42 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH43 : (1 <= current_length)) (PreH44 : (current_length <= number_width_pre)) (PreH45 : (1 <= pivot_length)) (PreH46 : (pivot_length <= number_width_pre)) (PreH47 : (total_length = (current_length + pivot_length))) (PreH48 : (comparison = (0 : Int))) (PreH49 : ((0 : Int) <= position)) (PreH50 : (position < total_length)) (PreH51 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH52 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH53 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH54 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH55 : ((sum (lens1)) = (sum (lens)))) (PreH56 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_11_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (pivot_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (pivot_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : ((0 : Int) <= (position - pivot_length))) (PreH8 : ((position - pivot_length) < number_width_pre)) (PreH9 : (left_digit <= INT_MAX)) (PreH10 : (comparison <= INT_MAX)) (PreH11 : (total_length <= INT_MAX)) (PreH12 : (current_length <= INT_MAX)) (PreH13 : (scan <= INT_MAX)) (PreH14 : (boundary <= INT_MAX)) (PreH15 : (high_pre <= INT_MAX)) (PreH16 : (low_pre <= INT_MAX)) (PreH17 : (count_pre <= INT_MAX)) (PreH18 : (left_digit >= INT_MIN)) (PreH19 : (comparison >= INT_MIN)) (PreH20 : (total_length >= INT_MIN)) (PreH21 : (current_length >= INT_MIN)) (PreH22 : (scan >= INT_MIN)) (PreH23 : (boundary >= INT_MIN)) (PreH24 : (high_pre >= INT_MIN)) (PreH25 : (low_pre >= INT_MIN)) (PreH26 : (count_pre >= INT_MIN)) (PreH27 : (position >= pivot_length)) (PreH28 : (1 <= count_pre)) (PreH29 : (count_pre <= 20)) (PreH30 : (1 <= number_width_pre)) (PreH31 : (number_width_pre <= 10)) (PreH32 : ((0 : Int) <= low_pre)) (PreH33 : (low_pre < high_pre)) (PreH34 : (high_pre < count_pre)) (PreH35 : ((low_pre - 1) <= boundary)) (PreH36 : (boundary < scan)) (PreH37 : (low_pre <= scan)) (PreH38 : (scan < high_pre)) (PreH39 : (1 <= (sum (lens)))) (PreH40 : ((sum (lens)) <= 200)) (PreH41 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH42 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH43 : (1 <= current_length)) (PreH44 : (current_length <= number_width_pre)) (PreH45 : (1 <= pivot_length)) (PreH46 : (pivot_length <= number_width_pre)) (PreH47 : (total_length = (current_length + pivot_length))) (PreH48 : (comparison = (0 : Int))) (PreH49 : ((0 : Int) <= position)) (PreH50 : (position < total_length)) (PreH51 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH52 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH53 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH54 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH55 : ((sum (lens1)) = (sum (lens)))) (PreH56 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_12_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + position))) (PreH2 : (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (pivot_length <= INT_MAX)) (PreH10 : (scan <= INT_MAX)) (PreH11 : (boundary <= INT_MAX)) (PreH12 : (high_pre <= INT_MAX)) (PreH13 : (low_pre <= INT_MAX)) (PreH14 : (count_pre <= INT_MAX)) (PreH15 : (left_digit >= INT_MIN)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (total_length >= INT_MIN)) (PreH18 : (current_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position < pivot_length)) (PreH26 : (1 <= count_pre)) (PreH27 : (count_pre <= 20)) (PreH28 : (1 <= number_width_pre)) (PreH29 : (number_width_pre <= 10)) (PreH30 : ((0 : Int) <= low_pre)) (PreH31 : (low_pre < high_pre)) (PreH32 : (high_pre < count_pre)) (PreH33 : ((low_pre - 1) <= boundary)) (PreH34 : (boundary < scan)) (PreH35 : (low_pre <= scan)) (PreH36 : (scan < high_pre)) (PreH37 : (1 <= (sum (lens)))) (PreH38 : ((sum (lens)) <= 200)) (PreH39 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH40 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH41 : (1 <= current_length)) (PreH42 : (current_length <= number_width_pre)) (PreH43 : (1 <= pivot_length)) (PreH44 : (pivot_length <= number_width_pre)) (PreH45 : (total_length = (current_length + pivot_length))) (PreH46 : (comparison = (0 : Int))) (PreH47 : ((0 : Int) <= position)) (PreH48 : (position < total_length)) (PreH49 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH50 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH53 : ((sum (lens1_2)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((high_pre * number_width_pre) + position) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + position))) (PreH2 : (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (pivot_length <= INT_MAX)) (PreH10 : (scan <= INT_MAX)) (PreH11 : (boundary <= INT_MAX)) (PreH12 : (high_pre <= INT_MAX)) (PreH13 : (low_pre <= INT_MAX)) (PreH14 : (count_pre <= INT_MAX)) (PreH15 : (left_digit >= INT_MIN)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (total_length >= INT_MIN)) (PreH18 : (current_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position < pivot_length)) (PreH26 : (1 <= count_pre)) (PreH27 : (count_pre <= 20)) (PreH28 : (1 <= number_width_pre)) (PreH29 : (number_width_pre <= 10)) (PreH30 : ((0 : Int) <= low_pre)) (PreH31 : (low_pre < high_pre)) (PreH32 : (high_pre < count_pre)) (PreH33 : ((low_pre - 1) <= boundary)) (PreH34 : (boundary < scan)) (PreH35 : (low_pre <= scan)) (PreH36 : (scan < high_pre)) (PreH37 : (1 <= (sum (lens)))) (PreH38 : ((sum (lens)) <= 200)) (PreH39 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH40 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH41 : (1 <= current_length)) (PreH42 : (current_length <= number_width_pre)) (PreH43 : (1 <= pivot_length)) (PreH44 : (pivot_length <= number_width_pre)) (PreH45 : (total_length = (current_length + pivot_length))) (PreH46 : (comparison = (0 : Int))) (PreH47 : ((0 : Int) <= position)) (PreH48 : (position < total_length)) (PreH49 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH50 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH53 : ((sum (lens1_2)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= position) ” &&
  “ ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((high_pre * number_width_pre) + position) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_12_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length)))) (PreH2 : (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - pivot_length))) (PreH4 : ((position - pivot_length) < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (left_digit >= INT_MIN)) (PreH15 : (comparison >= INT_MIN)) (PreH16 : (total_length >= INT_MIN)) (PreH17 : (current_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position >= pivot_length)) (PreH24 : (1 <= count_pre)) (PreH25 : (count_pre <= 20)) (PreH26 : (1 <= number_width_pre)) (PreH27 : (number_width_pre <= 10)) (PreH28 : ((0 : Int) <= low_pre)) (PreH29 : (low_pre < high_pre)) (PreH30 : (high_pre < count_pre)) (PreH31 : ((low_pre - 1) <= boundary)) (PreH32 : (boundary < scan)) (PreH33 : (low_pre <= scan)) (PreH34 : (scan < high_pre)) (PreH35 : (1 <= (sum (lens)))) (PreH36 : ((sum (lens)) <= 200)) (PreH37 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH38 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH39 : (1 <= current_length)) (PreH40 : (current_length <= number_width_pre)) (PreH41 : (1 <= pivot_length)) (PreH42 : (pivot_length <= number_width_pre)) (PreH43 : (total_length = (current_length + pivot_length))) (PreH44 : (comparison = (0 : Int))) (PreH45 : ((0 : Int) <= position)) (PreH46 : (position < total_length)) (PreH47 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH51 : ((sum (lens1_2)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((scan * number_width_pre) + (position - pivot_length)) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length)))) (PreH2 : (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - pivot_length))) (PreH4 : ((position - pivot_length) < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (left_digit >= INT_MIN)) (PreH15 : (comparison >= INT_MIN)) (PreH16 : (total_length >= INT_MIN)) (PreH17 : (current_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position >= pivot_length)) (PreH24 : (1 <= count_pre)) (PreH25 : (count_pre <= 20)) (PreH26 : (1 <= number_width_pre)) (PreH27 : (number_width_pre <= 10)) (PreH28 : ((0 : Int) <= low_pre)) (PreH29 : (low_pre < high_pre)) (PreH30 : (high_pre < count_pre)) (PreH31 : ((low_pre - 1) <= boundary)) (PreH32 : (boundary < scan)) (PreH33 : (low_pre <= scan)) (PreH34 : (scan < high_pre)) (PreH35 : (1 <= (sum (lens)))) (PreH36 : ((sum (lens)) <= 200)) (PreH37 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH38 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH39 : (1 <= current_length)) (PreH40 : (current_length <= number_width_pre)) (PreH41 : (1 <= pivot_length)) (PreH42 : (pivot_length <= number_width_pre)) (PreH43 : (total_length = (current_length + pivot_length))) (PreH44 : (comparison = (0 : Int))) (PreH45 : ((0 : Int) <= position)) (PreH46 : (position < total_length)) (PreH47 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH51 : ((sum (lens1_2)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((scan * number_width_pre) + (position - (Znth (high_pre) (lens1_2) ((0 : Int))))) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_13 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit = right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= (position + 1)) ” &&
  “ ((position + 1) <= total_length) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre (position + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit = right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= (position + 1)) ” &&
  “ ((position + 1) <= (current_length + pivot_length)) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre (position + 1)) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_14_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (position >= total_length)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position <= total_length)) (PreH25 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH26 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH27 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1 scan high_pre comparison) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (position >= total_length)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position <= total_length)) (PreH25 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH26 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH27 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1_2 scan high_pre (0 : Int)) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_14_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1 scan high_pre (left_digit - right_digit)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (comparison = (0 : Int))) (PreH23 : ((0 : Int) <= position)) (PreH24 : (position < total_length)) (PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH28 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH29 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1_2 scan high_pre ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) - (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_15 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre)) (PreH23 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH24 : (ConcatCompareOutcome rows1 lens1_2 scan high_pre comparison)) (PreH25 : ((sum (lens1_2)) = (sum (lens)))) (PreH26 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre ((boundary + 1) - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) scan (0 : Int) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre)) (PreH23 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH24 : (ConcatCompareOutcome rows1 lens1_2 scan high_pre comparison)) (PreH25 : ((sum (lens1_2)) = (sum (lens)))) (PreH26 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= scan) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre ((boundary + 1) - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) scan (0 : Int) number_width_pre) ” &&
  “ (FlatRows flat1 rows_now count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_16 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= boundary)) (PreH10 : (boundary <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : ((0 : Int) <= column)) (PreH13 : (column <= number_width_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH17 : (1 <= pivot_length)) (PreH18 : (pivot_length <= number_width_pre)) (PreH19 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH20 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH21 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH22 : (comparison > (0 : Int))) (PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((boundary * number_width_pre) + column)) ” &&
  “ (((boundary * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (comparison <= INT_MAX)) (PreH2 : (pivot_length <= INT_MAX)) (PreH3 : (column <= INT_MAX)) (PreH4 : (scan <= INT_MAX)) (PreH5 : (boundary <= INT_MAX)) (PreH6 : (high_pre <= INT_MAX)) (PreH7 : (low_pre <= INT_MAX)) (PreH8 : (number_width_pre <= INT_MAX)) (PreH9 : (count_pre <= INT_MAX)) (PreH10 : (comparison >= INT_MIN)) (PreH11 : (pivot_length >= INT_MIN)) (PreH12 : (column >= INT_MIN)) (PreH13 : (scan >= INT_MIN)) (PreH14 : (boundary >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (number_width_pre >= INT_MIN)) (PreH18 : (count_pre >= INT_MIN)) (PreH19 : (column < number_width_pre)) (PreH20 : (1 <= count_pre)) (PreH21 : (count_pre <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre < high_pre)) (PreH26 : (high_pre < count_pre)) (PreH27 : (low_pre <= boundary)) (PreH28 : (boundary <= scan)) (PreH29 : (scan < high_pre)) (PreH30 : ((0 : Int) <= column)) (PreH31 : (column <= number_width_pre)) (PreH32 : (1 <= (sum (lens)))) (PreH33 : ((sum (lens)) <= 200)) (PreH34 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH35 : (1 <= pivot_length)) (PreH36 : (pivot_length <= number_width_pre)) (PreH37 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH38 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH39 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH40 : (comparison > (0 : Int))) (PreH41 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((boundary * number_width_pre) + column) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_16_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (comparison <= INT_MAX)) (PreH2 : (pivot_length <= INT_MAX)) (PreH3 : (column <= INT_MAX)) (PreH4 : (scan <= INT_MAX)) (PreH5 : (boundary <= INT_MAX)) (PreH6 : (high_pre <= INT_MAX)) (PreH7 : (low_pre <= INT_MAX)) (PreH8 : (number_width_pre <= INT_MAX)) (PreH9 : (count_pre <= INT_MAX)) (PreH10 : (comparison >= INT_MIN)) (PreH11 : (pivot_length >= INT_MIN)) (PreH12 : (column >= INT_MIN)) (PreH13 : (scan >= INT_MIN)) (PreH14 : (boundary >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (number_width_pre >= INT_MIN)) (PreH18 : (count_pre >= INT_MIN)) (PreH19 : (column < number_width_pre)) (PreH20 : (1 <= count_pre)) (PreH21 : (count_pre <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre < high_pre)) (PreH26 : (high_pre < count_pre)) (PreH27 : (low_pre <= boundary)) (PreH28 : (boundary <= scan)) (PreH29 : (scan < high_pre)) (PreH30 : ((0 : Int) <= column)) (PreH31 : (column <= number_width_pre)) (PreH32 : (1 <= (sum (lens)))) (PreH33 : ((sum (lens)) <= 200)) (PreH34 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH35 : (1 <= pivot_length)) (PreH36 : (pivot_length <= number_width_pre)) (PreH37 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH38 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH39 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH40 : (comparison > (0 : Int))) (PreH41 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_17 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH2 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (comparison <= INT_MAX)) (PreH4 : (pivot_length <= INT_MAX)) (PreH5 : (scan <= INT_MAX)) (PreH6 : (high_pre <= INT_MAX)) (PreH7 : (low_pre <= INT_MAX)) (PreH8 : (comparison >= INT_MIN)) (PreH9 : (pivot_length >= INT_MIN)) (PreH10 : (scan >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= boundary)) (PreH22 : (boundary <= scan)) (PreH23 : (scan < high_pre)) (PreH24 : ((0 : Int) <= column)) (PreH25 : (column <= number_width_pre)) (PreH26 : (1 <= (sum (lens)))) (PreH27 : ((sum (lens)) <= 200)) (PreH28 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH29 : (1 <= pivot_length)) (PreH30 : (pivot_length <= number_width_pre)) (PreH31 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH32 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH33 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH34 : (comparison > (0 : Int))) (PreH35 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH36 : ((sum (lens1)) = (sum (lens)))) (PreH37 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + column)) ” &&
  “ (((scan * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ ((0 : Int) <= ((boundary * number_width_pre) + column)) ” &&
  “ (((boundary * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (count_pre <= INT_MAX)) (PreH2 : (column <= INT_MAX)) (PreH3 : (number_width_pre <= INT_MAX)) (PreH4 : (boundary <= INT_MAX)) (PreH5 : (count_pre >= INT_MIN)) (PreH6 : (column >= INT_MIN)) (PreH7 : (number_width_pre >= INT_MIN)) (PreH8 : (boundary >= INT_MIN)) (PreH9 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH10 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH11 : (comparison <= INT_MAX)) (PreH12 : (pivot_length <= INT_MAX)) (PreH13 : (scan <= INT_MAX)) (PreH14 : (high_pre <= INT_MAX)) (PreH15 : (low_pre <= INT_MAX)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (high_pre >= INT_MIN)) (PreH20 : (low_pre >= INT_MIN)) (PreH21 : (column < number_width_pre)) (PreH22 : (1 <= count_pre)) (PreH23 : (count_pre <= 20)) (PreH24 : (1 <= number_width_pre)) (PreH25 : (number_width_pre <= 10)) (PreH26 : ((0 : Int) <= low_pre)) (PreH27 : (low_pre < high_pre)) (PreH28 : (high_pre < count_pre)) (PreH29 : (low_pre <= boundary)) (PreH30 : (boundary <= scan)) (PreH31 : (scan < high_pre)) (PreH32 : ((0 : Int) <= column)) (PreH33 : (column <= number_width_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH37 : (1 <= pivot_length)) (PreH38 : (pivot_length <= number_width_pre)) (PreH39 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH40 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH41 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH42 : (comparison > (0 : Int))) (PreH43 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((scan * number_width_pre) + column) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_17_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (count_pre <= INT_MAX)) (PreH2 : (column <= INT_MAX)) (PreH3 : (number_width_pre <= INT_MAX)) (PreH4 : (boundary <= INT_MAX)) (PreH5 : (count_pre >= INT_MIN)) (PreH6 : (column >= INT_MIN)) (PreH7 : (number_width_pre >= INT_MIN)) (PreH8 : (boundary >= INT_MIN)) (PreH9 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH10 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH11 : (comparison <= INT_MAX)) (PreH12 : (pivot_length <= INT_MAX)) (PreH13 : (scan <= INT_MAX)) (PreH14 : (high_pre <= INT_MAX)) (PreH15 : (low_pre <= INT_MAX)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (high_pre >= INT_MIN)) (PreH20 : (low_pre >= INT_MIN)) (PreH21 : (column < number_width_pre)) (PreH22 : (1 <= count_pre)) (PreH23 : (count_pre <= 20)) (PreH24 : (1 <= number_width_pre)) (PreH25 : (number_width_pre <= 10)) (PreH26 : ((0 : Int) <= low_pre)) (PreH27 : (low_pre < high_pre)) (PreH28 : (high_pre < count_pre)) (PreH29 : (low_pre <= boundary)) (PreH30 : (boundary <= scan)) (PreH31 : (scan < high_pre)) (PreH32 : ((0 : Int) <= column)) (PreH33 : (column <= number_width_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH37 : (1 <= pivot_length)) (PreH38 : (pivot_length <= number_width_pre)) (PreH39 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH40 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH41 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH42 : (comparison > (0 : Int))) (PreH43 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (((scan * number_width_pre) + column) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_18 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (comparison : Int) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before_2 lens1_2 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before_2 rows_now_2 boundary scan column number_width_pre)) (PreH40 : ((sum (lens1_2)) = (sum (lens)))) (PreH41 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((scan * number_width_pre) + column)) ((Znth ((boundary * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))))
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan (column + 1) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (comparison : Int) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before_2 lens1_2 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before_2 rows_now_2 boundary scan column number_width_pre)) (PreH40 : ((sum (lens1_2)) = (sum (lens)))) (PreH41 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan (column + 1) number_width_pre) ” &&
  “ (FlatRows (replace_Znth (((scan * number_width_pre) + column)) ((Znth ((boundary * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))) rows_now count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_19_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= boundary)) (PreH10 : (boundary <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : ((0 : Int) <= column)) (PreH13 : (column <= number_width_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= pivot_length)) (PreH18 : (pivot_length <= number_width_pre)) (PreH19 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre)) (PreH20 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH21 : (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison)) (PreH22 : (comparison > (0 : Int))) (PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH24 : ((sum (lens1_2)) = (sum (lens)))) (PreH25 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "comparison" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= boundary)) (PreH10 : (boundary <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : ((0 : Int) <= column)) (PreH13 : (column <= number_width_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= pivot_length)) (PreH18 : (pivot_length <= number_width_pre)) (PreH19 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre)) (PreH20 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH21 : (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison)) (PreH22 : (comparison > (0 : Int))) (PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH24 : ((sum (lens1_2)) = (sum (lens)))) (PreH25 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((low_pre - 1) <= boundary) ” &&
  “ ((Znth (high_pre) (lens1_2) ((0 : Int))) = (Znth (high_pre) ((replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2))))) ((0 : Int)))) ” &&
  “ (RowsWellFormed rows1 (replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))) count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens (replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))) low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum ((replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))))) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_19_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison <= (0 : Int))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH23 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH24 : (ConcatCompareOutcome rows1_2 lens1_2 scan high_pre comparison)) (PreH25 : ((sum (lens1_2)) = (sum (lens)))) (PreH26 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "comparison" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison <= (0 : Int))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH17 : (1 <= current_length)) (PreH18 : (current_length <= number_width_pre)) (PreH19 : (1 <= pivot_length)) (PreH20 : (pivot_length <= number_width_pre)) (PreH21 : (total_length = (current_length + pivot_length))) (PreH22 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH23 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH24 : (ConcatCompareOutcome rows1_2 lens1_2 scan high_pre comparison)) (PreH25 : ((sum (lens1_2)) = (sum (lens)))) (PreH26 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (boundary <= scan) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary (scan + 1)) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_20 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre < high_pre)) (PreH7 : (high_pre < count_pre)) (PreH8 : ((low_pre - 1) <= boundary)) (PreH9 : (boundary <= scan)) (PreH10 : (scan < high_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH14 : (1 <= pivot_length)) (PreH15 : (pivot_length <= number_width_pre)) (PreH16 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH17 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary (scan + 1))) (PreH18 : ((sum (lens1_2)) = (sum (lens)))) (PreH19 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < (scan + 1)) ” &&
  “ (low_pre <= (scan + 1)) ” &&
  “ ((scan + 1) <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre < high_pre)) (PreH7 : (high_pre < count_pre)) (PreH8 : ((low_pre - 1) <= boundary)) (PreH9 : (boundary <= scan)) (PreH10 : (scan < high_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH14 : (1 <= pivot_length)) (PreH15 : (pivot_length <= number_width_pre)) (PreH16 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH17 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary (scan + 1))) (PreH18 : ((sum (lens1_2)) = (sum (lens)))) (PreH19 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (boundary < (scan + 1)) ” &&
  “ (low_pre <= (scan + 1)) ” &&
  “ ((scan + 1) <= high_pre) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary (scan + 1)) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_21 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1_2)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= high_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre ((boundary + 1) - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) high_pre (0 : Int) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1_2)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= high_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre ((boundary + 1) - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) high_pre (0 : Int) number_width_pre) ” &&
  “ (FlatRows flat1 rows_now count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_22 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : ((0 : Int) <= column)) (PreH12 : (column <= number_width_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH20 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH21 : ((sum (lens1)) = (sum (lens)))) (PreH22 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((pivot * number_width_pre) + column)) ” &&
  “ (((pivot * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (pivot_length <= INT_MAX)) (PreH2 : (column <= INT_MAX)) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (high_pre <= INT_MAX)) (PreH5 : (low_pre <= INT_MAX)) (PreH6 : (number_width_pre <= INT_MAX)) (PreH7 : (count_pre <= INT_MAX)) (PreH8 : (pivot_length >= INT_MIN)) (PreH9 : (column >= INT_MIN)) (PreH10 : (pivot >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (number_width_pre >= INT_MIN)) (PreH14 : (count_pre >= INT_MIN)) (PreH15 : (column < number_width_pre)) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : ((0 : Int) <= low_pre)) (PreH21 : (low_pre < high_pre)) (PreH22 : (high_pre < count_pre)) (PreH23 : (low_pre <= pivot)) (PreH24 : (pivot <= high_pre)) (PreH25 : ((0 : Int) <= column)) (PreH26 : (column <= number_width_pre)) (PreH27 : (1 <= (sum (lens)))) (PreH28 : ((sum (lens)) <= 200)) (PreH29 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH30 : (1 <= pivot_length)) (PreH31 : (pivot_length <= number_width_pre)) (PreH32 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH33 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH34 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH35 : ((sum (lens1)) = (sum (lens)))) (PreH36 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((pivot * number_width_pre) + column) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_22_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (pivot_length <= INT_MAX)) (PreH2 : (column <= INT_MAX)) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (high_pre <= INT_MAX)) (PreH5 : (low_pre <= INT_MAX)) (PreH6 : (number_width_pre <= INT_MAX)) (PreH7 : (count_pre <= INT_MAX)) (PreH8 : (pivot_length >= INT_MIN)) (PreH9 : (column >= INT_MIN)) (PreH10 : (pivot >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (number_width_pre >= INT_MIN)) (PreH14 : (count_pre >= INT_MIN)) (PreH15 : (column < number_width_pre)) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : ((0 : Int) <= low_pre)) (PreH21 : (low_pre < high_pre)) (PreH22 : (high_pre < count_pre)) (PreH23 : (low_pre <= pivot)) (PreH24 : (pivot <= high_pre)) (PreH25 : ((0 : Int) <= column)) (PreH26 : (column <= number_width_pre)) (PreH27 : (1 <= (sum (lens)))) (PreH28 : ((sum (lens)) <= 200)) (PreH29 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH30 : (1 <= pivot_length)) (PreH31 : (pivot_length <= number_width_pre)) (PreH32 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH33 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH34 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH35 : ((sum (lens1)) = (sum (lens)))) (PreH36 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_23 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH2 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot_length <= INT_MAX)) (PreH4 : (high_pre <= INT_MAX)) (PreH5 : (low_pre <= INT_MAX)) (PreH6 : (pivot_length >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (column < number_width_pre)) (PreH10 : (1 <= count_pre)) (PreH11 : (count_pre <= 20)) (PreH12 : (1 <= number_width_pre)) (PreH13 : (number_width_pre <= 10)) (PreH14 : ((0 : Int) <= low_pre)) (PreH15 : (low_pre < high_pre)) (PreH16 : (high_pre < count_pre)) (PreH17 : (low_pre <= pivot)) (PreH18 : (pivot <= high_pre)) (PreH19 : ((0 : Int) <= column)) (PreH20 : (column <= number_width_pre)) (PreH21 : (1 <= (sum (lens)))) (PreH22 : ((sum (lens)) <= 200)) (PreH23 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH27 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH28 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + column)) ” &&
  “ (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot <= INT_MAX) ” &&
  “ (pivot >= INT_MIN) ” &&
  “ ((0 : Int) <= ((pivot * number_width_pre) + column)) ” &&
  “ (((pivot * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (count_pre <= INT_MAX)) (PreH2 : (column <= INT_MAX)) (PreH3 : (number_width_pre <= INT_MAX)) (PreH4 : (pivot <= INT_MAX)) (PreH5 : (count_pre >= INT_MIN)) (PreH6 : (column >= INT_MIN)) (PreH7 : (number_width_pre >= INT_MIN)) (PreH8 : (pivot >= INT_MIN)) (PreH9 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH10 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH11 : (pivot_length <= INT_MAX)) (PreH12 : (high_pre <= INT_MAX)) (PreH13 : (low_pre <= INT_MAX)) (PreH14 : (pivot_length >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= pivot)) (PreH26 : (pivot <= high_pre)) (PreH27 : ((0 : Int) <= column)) (PreH28 : (column <= number_width_pre)) (PreH29 : (1 <= (sum (lens)))) (PreH30 : ((sum (lens)) <= 200)) (PreH31 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH32 : (1 <= pivot_length)) (PreH33 : (pivot_length <= number_width_pre)) (PreH34 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH35 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH36 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH37 : ((sum (lens1)) = (sum (lens)))) (PreH38 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_23_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (count_pre <= INT_MAX)) (PreH2 : (column <= INT_MAX)) (PreH3 : (number_width_pre <= INT_MAX)) (PreH4 : (pivot <= INT_MAX)) (PreH5 : (count_pre >= INT_MIN)) (PreH6 : (column >= INT_MIN)) (PreH7 : (number_width_pre >= INT_MIN)) (PreH8 : (pivot >= INT_MIN)) (PreH9 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH10 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH11 : (pivot_length <= INT_MAX)) (PreH12 : (high_pre <= INT_MAX)) (PreH13 : (low_pre <= INT_MAX)) (PreH14 : (pivot_length >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= pivot)) (PreH26 : (pivot <= high_pre)) (PreH27 : ((0 : Int) <= column)) (PreH28 : (column <= number_width_pre)) (PreH29 : (1 <= (sum (lens)))) (PreH30 : ((sum (lens)) <= 200)) (PreH31 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH32 : (1 <= pivot_length)) (PreH33 : (pivot_length <= number_width_pre)) (PreH34 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH35 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH36 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH37 : ((sum (lens1)) = (sum (lens)))) (PreH38 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))

noncomputable def quicksort_numbers_entail_wit_24 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before_2 rows_now_2 pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((high_pre * number_width_pre) + column)) ((Znth ((pivot * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))))
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre (column + 1) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before_2 rows_now_2 pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1_2 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre (column + 1) number_width_pre) ” &&
  “ (FlatRows (replace_Znth (((high_pre * number_width_pre) + column)) ((Znth ((pivot * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))) rows_now count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_25 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : ((0 : Int) <= column)) (PreH12 : (column <= number_width_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH20 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (pivot) (pivot_length) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot_length" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : ((0 : Int) <= column)) (PreH12 : (column <= number_width_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH20 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))) count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2))))) ” &&
  “ (SameOutsidePairedRange rows rows1 lens (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))) low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))) low_pre high_pre pivot) ” &&
  “ ((sum ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))))) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (lens1_3 : (List Int)) (PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre)) (PreH2 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows2 rows1_3 lens2 lens1_3)) (PreH4 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1) high_pre)) (PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH6 : ((sum (lens1_3)) = (sum (lens2)))) (PreH7 : (pivot < high_pre)) (PreH8 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH9 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH10 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH11 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH12 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH13 : ((sum (lens2)) = (sum (lens1_2)))) (PreH14 : (pivot > low_pre)) (PreH15 : (1 <= count_pre)) (PreH16 : (count_pre <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : ((0 : Int) <= low_pre)) (PreH20 : (low_pre < high_pre)) (PreH21 : (high_pre < count_pre)) (PreH22 : (low_pre <= pivot)) (PreH23 : (pivot <= high_pre)) (PreH24 : (1 <= (sum (lens)))) (PreH25 : ((sum (lens)) <= 200)) (PreH26 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH27 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH28 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH29 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_3)
  ** (intArray.full lengths_pre count_pre lens1_3)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (lens1_3 : (List Int)) (PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre)) (PreH2 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows2 rows1_3 lens2 lens1_3)) (PreH4 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1) high_pre)) (PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH6 : ((sum (lens1_3)) = (sum (lens2)))) (PreH7 : (pivot < high_pre)) (PreH8 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH9 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH10 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH11 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH12 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH13 : ((sum (lens2)) = (sum (lens1_2)))) (PreH14 : (pivot > low_pre)) (PreH15 : (1 <= count_pre)) (PreH16 : (count_pre <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : ((0 : Int) <= low_pre)) (PreH20 : (low_pre < high_pre)) (PreH21 : (high_pre < count_pre)) (PreH22 : (low_pre <= pivot)) (PreH23 : (pivot <= high_pre)) (PreH24 : (1 <= (sum (lens)))) (PreH25 : ((sum (lens)) <= 200)) (PreH26 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH27 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH28 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH29 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens1_3 count_pre number_width_pre) ” &&
  “ (FlatRows flat1_3 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_3) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1_3 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1_3 low_pre high_pre) ” &&
  “ ((sum (lens1_3)) = (sum (lens))) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot >= high_pre)) (PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH3 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH4 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH5 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH7 : ((sum (lens2)) = (sum (lens1_2)))) (PreH8 : (pivot > low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH24 : ((sum (lens1_2)) = (sum (lens)))) (PreH25 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot >= high_pre)) (PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH3 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH4 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH5 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH7 : ((sum (lens2)) = (sum (lens1_2)))) (PreH8 : (pivot > low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH24 : ((sum (lens1_2)) = (sum (lens)))) (PreH25 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens2 count_pre number_width_pre) ” &&
  “ (FlatRows flat2 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens2) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens2 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens2 low_pre high_pre) ” &&
  “ ((sum (lens2)) = (sum (lens))) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_3 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (lens1_3 : (List Int)) (PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre)) (PreH2 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3)) (PreH4 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1) high_pre)) (PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH6 : ((sum (lens1_3)) = (sum (lens1_2)))) (PreH7 : (pivot < high_pre)) (PreH8 : (pivot <= low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH24 : ((sum (lens1_2)) = (sum (lens)))) (PreH25 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_3)
  ** (intArray.full lengths_pre count_pre lens1_3)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (lens1_3 : (List Int)) (PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre)) (PreH2 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3)) (PreH4 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1) high_pre)) (PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH6 : ((sum (lens1_3)) = (sum (lens1_2)))) (PreH7 : (pivot < high_pre)) (PreH8 : (pivot <= low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH24 : ((sum (lens1_2)) = (sum (lens)))) (PreH25 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens1_3 count_pre number_width_pre) ” &&
  “ (FlatRows flat1_3 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_3) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1_3 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1_3 low_pre high_pre) ” &&
  “ ((sum (lens1_3)) = (sum (lens))) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_4 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (low_pre >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre <= count_pre)) (PreH9 : ((-1) <= high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH14 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (low_pre >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre <= count_pre)) (PreH9 : ((-1) <= high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH14 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens count_pre number_width_pre) ” &&
  “ (FlatRows flat rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens low_pre high_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_partial_solve_wit_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ (high_pre < count_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows lens count_pre number_width_pre) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ”
  &&  (((lengths_pre + (high_pre * sizeof(INT)))) # Int |-> ((Znth high_pre lens (0 : Int))))
  ** (intArray.missing_i lengths_pre high_pre (0 : Int) count_pre lens)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)

noncomputable def quicksort_numbers_partial_solve_wit_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : ((low_pre - 1) <= boundary)) (PreH10 : (boundary < scan)) (PreH11 : (low_pre <= scan)) (PreH12 : (scan <= high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH20 : ((sum (lens1)) = (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (scan < high_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre scan (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)

noncomputable def quicksort_numbers_partial_solve_wit_3 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + position))) (PreH2 : (((scan * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (current_length <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (comparison >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (current_length >= INT_MIN)) (PreH17 : (pivot_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position < current_length)) (PreH24 : (position < total_length)) (PreH25 : (1 <= count_pre)) (PreH26 : (count_pre <= 20)) (PreH27 : (1 <= number_width_pre)) (PreH28 : (number_width_pre <= 10)) (PreH29 : ((0 : Int) <= low_pre)) (PreH30 : (low_pre < high_pre)) (PreH31 : (high_pre < count_pre)) (PreH32 : ((low_pre - 1) <= boundary)) (PreH33 : (boundary < scan)) (PreH34 : (low_pre <= scan)) (PreH35 : (scan < high_pre)) (PreH36 : (1 <= (sum (lens)))) (PreH37 : ((sum (lens)) <= 200)) (PreH38 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH39 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH40 : (1 <= current_length)) (PreH41 : (current_length <= number_width_pre)) (PreH42 : (1 <= pivot_length)) (PreH43 : (pivot_length <= number_width_pre)) (PreH44 : (total_length = (current_length + pivot_length))) (PreH45 : (comparison = (0 : Int))) (PreH46 : ((0 : Int) <= position)) (PreH47 : (position <= total_length)) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + position)) ” &&
  “ (((scan * number_width_pre) + position) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < number_width_pre) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position < current_length) ” &&
  “ (position < total_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + position) * sizeof(INT)))) # Int |-> ((Znth ((scan * number_width_pre) + position) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + position) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_4 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length)))) (PreH2 : (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - current_length))) (PreH4 : ((position - current_length) < number_width_pre)) (PreH5 : (comparison <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (scan <= INT_MAX)) (PreH9 : (boundary <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (count_pre <= INT_MAX)) (PreH13 : (comparison >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (pivot_length >= INT_MIN)) (PreH16 : (scan >= INT_MIN)) (PreH17 : (boundary >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (count_pre >= INT_MIN)) (PreH21 : (position >= current_length)) (PreH22 : (position < total_length)) (PreH23 : (1 <= count_pre)) (PreH24 : (count_pre <= 20)) (PreH25 : (1 <= number_width_pre)) (PreH26 : (number_width_pre <= 10)) (PreH27 : ((0 : Int) <= low_pre)) (PreH28 : (low_pre < high_pre)) (PreH29 : (high_pre < count_pre)) (PreH30 : ((low_pre - 1) <= boundary)) (PreH31 : (boundary < scan)) (PreH32 : (low_pre <= scan)) (PreH33 : (scan < high_pre)) (PreH34 : (1 <= (sum (lens)))) (PreH35 : ((sum (lens)) <= 200)) (PreH36 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH37 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH38 : (1 <= current_length)) (PreH39 : (current_length <= number_width_pre)) (PreH40 : (1 <= pivot_length)) (PreH41 : (pivot_length <= number_width_pre)) (PreH42 : (total_length = (current_length + pivot_length))) (PreH43 : (comparison = (0 : Int))) (PreH44 : ((0 : Int) <= position)) (PreH45 : (position <= total_length)) (PreH46 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH47 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH48 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH49 : ((sum (lens1)) = (sum (lens)))) (PreH50 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + (position - current_length))) ” &&
  “ (((high_pre * number_width_pre) + (position - current_length)) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (position - current_length)) ” &&
  “ ((position - current_length) < number_width_pre) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position >= current_length) ” &&
  “ (position < total_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + (position - current_length)) * sizeof(INT)))) # Int |-> ((Znth ((high_pre * number_width_pre) + (position - current_length)) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + (position - current_length)) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_5 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + position))) (PreH2 : (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (pivot_length <= INT_MAX)) (PreH10 : (scan <= INT_MAX)) (PreH11 : (boundary <= INT_MAX)) (PreH12 : (high_pre <= INT_MAX)) (PreH13 : (low_pre <= INT_MAX)) (PreH14 : (count_pre <= INT_MAX)) (PreH15 : (left_digit >= INT_MIN)) (PreH16 : (comparison >= INT_MIN)) (PreH17 : (total_length >= INT_MIN)) (PreH18 : (current_length >= INT_MIN)) (PreH19 : (pivot_length >= INT_MIN)) (PreH20 : (scan >= INT_MIN)) (PreH21 : (boundary >= INT_MIN)) (PreH22 : (high_pre >= INT_MIN)) (PreH23 : (low_pre >= INT_MIN)) (PreH24 : (count_pre >= INT_MIN)) (PreH25 : (position < pivot_length)) (PreH26 : (1 <= count_pre)) (PreH27 : (count_pre <= 20)) (PreH28 : (1 <= number_width_pre)) (PreH29 : (number_width_pre <= 10)) (PreH30 : ((0 : Int) <= low_pre)) (PreH31 : (low_pre < high_pre)) (PreH32 : (high_pre < count_pre)) (PreH33 : ((low_pre - 1) <= boundary)) (PreH34 : (boundary < scan)) (PreH35 : (low_pre <= scan)) (PreH36 : (scan < high_pre)) (PreH37 : (1 <= (sum (lens)))) (PreH38 : ((sum (lens)) <= 200)) (PreH39 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH40 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH41 : (1 <= current_length)) (PreH42 : (current_length <= number_width_pre)) (PreH43 : (1 <= pivot_length)) (PreH44 : (pivot_length <= number_width_pre)) (PreH45 : (total_length = (current_length + pivot_length))) (PreH46 : (comparison = (0 : Int))) (PreH47 : ((0 : Int) <= position)) (PreH48 : (position < total_length)) (PreH49 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH50 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH51 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH52 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH53 : ((sum (lens1)) = (sum (lens)))) (PreH54 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + position)) ” &&
  “ (((high_pre * number_width_pre) + position) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < number_width_pre) ” &&
  “ (left_digit <= INT_MAX) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (left_digit >= INT_MIN) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position < pivot_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + position) * sizeof(INT)))) # Int |-> ((Znth ((high_pre * number_width_pre) + position) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + position) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_6 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length)))) (PreH2 : (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (position - pivot_length))) (PreH4 : ((position - pivot_length) < number_width_pre)) (PreH5 : (left_digit <= INT_MAX)) (PreH6 : (comparison <= INT_MAX)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (current_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (boundary <= INT_MAX)) (PreH11 : (high_pre <= INT_MAX)) (PreH12 : (low_pre <= INT_MAX)) (PreH13 : (count_pre <= INT_MAX)) (PreH14 : (left_digit >= INT_MIN)) (PreH15 : (comparison >= INT_MIN)) (PreH16 : (total_length >= INT_MIN)) (PreH17 : (current_length >= INT_MIN)) (PreH18 : (scan >= INT_MIN)) (PreH19 : (boundary >= INT_MIN)) (PreH20 : (high_pre >= INT_MIN)) (PreH21 : (low_pre >= INT_MIN)) (PreH22 : (count_pre >= INT_MIN)) (PreH23 : (position >= pivot_length)) (PreH24 : (1 <= count_pre)) (PreH25 : (count_pre <= 20)) (PreH26 : (1 <= number_width_pre)) (PreH27 : (number_width_pre <= 10)) (PreH28 : ((0 : Int) <= low_pre)) (PreH29 : (low_pre < high_pre)) (PreH30 : (high_pre < count_pre)) (PreH31 : ((low_pre - 1) <= boundary)) (PreH32 : (boundary < scan)) (PreH33 : (low_pre <= scan)) (PreH34 : (scan < high_pre)) (PreH35 : (1 <= (sum (lens)))) (PreH36 : ((sum (lens)) <= 200)) (PreH37 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH38 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH39 : (1 <= current_length)) (PreH40 : (current_length <= number_width_pre)) (PreH41 : (1 <= pivot_length)) (PreH42 : (pivot_length <= number_width_pre)) (PreH43 : (total_length = (current_length + pivot_length))) (PreH44 : (comparison = (0 : Int))) (PreH45 : ((0 : Int) <= position)) (PreH46 : (position < total_length)) (PreH47 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH48 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH49 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH50 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH51 : ((sum (lens1)) = (sum (lens)))) (PreH52 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + (position - pivot_length))) ” &&
  “ (((scan * number_width_pre) + (position - pivot_length)) < (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (position - pivot_length)) ” &&
  “ ((position - pivot_length) < number_width_pre) ” &&
  “ (left_digit <= INT_MAX) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (total_length <= INT_MAX) ” &&
  “ (current_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (left_digit >= INT_MIN) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (total_length >= INT_MIN) ” &&
  “ (current_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (position >= pivot_length) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + (position - pivot_length)) * sizeof(INT)))) # Int |-> ((Znth ((scan * number_width_pre) + (position - pivot_length)) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + (position - pivot_length)) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_7 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + column)) ” &&
  “ (((scan * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ ((0 : Int) <= ((boundary * number_width_pre) + column)) ” &&
  “ (((boundary * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((boundary * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((boundary * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_8 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + column)) ” &&
  “ (((scan * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ ((0 : Int) <= ((boundary * number_width_pre) + column)) ” &&
  “ (((boundary * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_9 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + column)) ” &&
  “ (((scan * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ ((0 : Int) <= ((boundary * number_width_pre) + column)) ” &&
  “ (((boundary * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((boundary * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((boundary * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_10 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : ((0 : Int) <= ((scan * number_width_pre) + column))) (PreH2 : (((scan * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (boundary <= INT_MAX)) (PreH4 : (boundary >= INT_MIN)) (PreH5 : ((0 : Int) <= ((boundary * number_width_pre) + column))) (PreH6 : (((boundary * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (comparison <= INT_MAX)) (PreH8 : (pivot_length <= INT_MAX)) (PreH9 : (scan <= INT_MAX)) (PreH10 : (high_pre <= INT_MAX)) (PreH11 : (low_pre <= INT_MAX)) (PreH12 : (comparison >= INT_MIN)) (PreH13 : (pivot_length >= INT_MIN)) (PreH14 : (scan >= INT_MIN)) (PreH15 : (high_pre >= INT_MIN)) (PreH16 : (low_pre >= INT_MIN)) (PreH17 : (column < number_width_pre)) (PreH18 : (1 <= count_pre)) (PreH19 : (count_pre <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : ((0 : Int) <= low_pre)) (PreH23 : (low_pre < high_pre)) (PreH24 : (high_pre < count_pre)) (PreH25 : (low_pre <= boundary)) (PreH26 : (boundary <= scan)) (PreH27 : (scan < high_pre)) (PreH28 : ((0 : Int) <= column)) (PreH29 : (column <= number_width_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH33 : (1 <= pivot_length)) (PreH34 : (pivot_length <= number_width_pre)) (PreH35 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH36 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH37 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH38 : (comparison > (0 : Int))) (PreH39 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH40 : ((sum (lens1)) = (sum (lens)))) (PreH41 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((scan * number_width_pre) + column)) ” &&
  “ (((scan * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (boundary <= INT_MAX) ” &&
  “ (boundary >= INT_MIN) ” &&
  “ ((0 : Int) <= ((boundary * number_width_pre) + column)) ” &&
  “ (((boundary * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (comparison <= INT_MAX) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (scan <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (comparison >= INT_MIN) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (scan >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_11 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= boundary)) (PreH10 : (boundary <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : ((0 : Int) <= column)) (PreH13 : (column <= number_width_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH17 : (1 <= pivot_length)) (PreH18 : (pivot_length <= number_width_pre)) (PreH19 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH20 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH21 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH22 : (comparison > (0 : Int))) (PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column >= number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (boundary * sizeof(INT)))) # Int |-> ((Znth boundary lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre boundary (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_12 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= boundary)) (PreH10 : (boundary <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : ((0 : Int) <= column)) (PreH13 : (column <= number_width_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH17 : (1 <= pivot_length)) (PreH18 : (pivot_length <= number_width_pre)) (PreH19 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH20 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH21 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH22 : (comparison > (0 : Int))) (PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre scan (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_13 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= boundary)) (PreH10 : (boundary <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : ((0 : Int) <= column)) (PreH13 : (column <= number_width_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH17 : (1 <= pivot_length)) (PreH18 : (pivot_length <= number_width_pre)) (PreH19 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH20 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH21 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH22 : (comparison > (0 : Int))) (PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (boundary * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre boundary (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_14 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= boundary)) (PreH10 : (boundary <= scan)) (PreH11 : (scan < high_pre)) (PreH12 : ((0 : Int) <= column)) (PreH13 : (column <= number_width_pre)) (PreH14 : (1 <= (sum (lens)))) (PreH15 : ((sum (lens)) <= 200)) (PreH16 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH17 : (1 <= pivot_length)) (PreH18 : (pivot_length <= number_width_pre)) (PreH19 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH20 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH21 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH22 : (comparison > (0 : Int))) (PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (boundary) ((Znth scan lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre scan (0 : Int) count_pre (replace_Znth (boundary) ((Znth scan lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_15 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + column)) ” &&
  “ (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot <= INT_MAX) ” &&
  “ (pivot >= INT_MIN) ” &&
  “ ((0 : Int) <= ((pivot * number_width_pre) + column)) ” &&
  “ (((pivot * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((pivot * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((pivot * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_16 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + column)) ” &&
  “ (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot <= INT_MAX) ” &&
  “ (pivot >= INT_MIN) ” &&
  “ ((0 : Int) <= ((pivot * number_width_pre) + column)) ” &&
  “ (((pivot * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_17 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + column)) ” &&
  “ (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot <= INT_MAX) ” &&
  “ (pivot >= INT_MIN) ” &&
  “ ((0 : Int) <= ((pivot * number_width_pre) + column)) ” &&
  “ (((pivot * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((pivot * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((pivot * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_18 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : ((0 : Int) <= ((high_pre * number_width_pre) + column))) (PreH2 : (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH3 : (pivot <= INT_MAX)) (PreH4 : (pivot >= INT_MIN)) (PreH5 : ((0 : Int) <= ((pivot * number_width_pre) + column))) (PreH6 : (((pivot * number_width_pre) + column) < (count_pre * number_width_pre))) (PreH7 : (pivot_length <= INT_MAX)) (PreH8 : (high_pre <= INT_MAX)) (PreH9 : (low_pre <= INT_MAX)) (PreH10 : (pivot_length >= INT_MIN)) (PreH11 : (high_pre >= INT_MIN)) (PreH12 : (low_pre >= INT_MIN)) (PreH13 : (column < number_width_pre)) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : ((0 : Int) <= low_pre)) (PreH19 : (low_pre < high_pre)) (PreH20 : (high_pre < count_pre)) (PreH21 : (low_pre <= pivot)) (PreH22 : (pivot <= high_pre)) (PreH23 : ((0 : Int) <= column)) (PreH24 : (column <= number_width_pre)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH28 : (1 <= pivot_length)) (PreH29 : (pivot_length <= number_width_pre)) (PreH30 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ ((0 : Int) <= ((high_pre * number_width_pre) + column)) ” &&
  “ (((high_pre * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot <= INT_MAX) ” &&
  “ (pivot >= INT_MIN) ” &&
  “ ((0 : Int) <= ((pivot * number_width_pre) + column)) ” &&
  “ (((pivot * number_width_pre) + column) < (count_pre * number_width_pre)) ” &&
  “ (pivot_length <= INT_MAX) ” &&
  “ (high_pre <= INT_MAX) ” &&
  “ (low_pre <= INT_MAX) ” &&
  “ (pivot_length >= INT_MIN) ” &&
  “ (high_pre >= INT_MIN) ” &&
  “ (low_pre >= INT_MIN) ” &&
  “ (column < number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_19 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : ((0 : Int) <= column)) (PreH12 : (column <= number_width_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH20 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH21 : ((sum (lens1)) = (sum (lens)))) (PreH22 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column >= number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (pivot * sizeof(INT)))) # Int |-> ((Znth pivot lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre pivot (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_20 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : ((0 : Int) <= column)) (PreH12 : (column <= number_width_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH20 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH21 : ((sum (lens1)) = (sum (lens)))) (PreH22 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (high_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre high_pre (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_21 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : ((0 : Int) <= column)) (PreH12 : (column <= number_width_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : (RowsWellFormed rows_before lens1 count_pre number_width_pre)) (PreH19 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH20 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH21 : ((sum (lens1)) = (sum (lens)))) (PreH22 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (high_pre) ((Znth pivot lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (RowsWellFormed rows_before lens1 count_pre number_width_pre) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (pivot * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre pivot (0 : Int) count_pre (replace_Znth (high_pre) ((Znth pivot lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_22_pure : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH14 : (PairedPermutation rows rows1 lens lens1)) (PreH15 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH16 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH17 : ((sum (lens1)) = (sum (lens)))) (PreH18 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= count_pre) ” &&
  “ ((-1) <= (pivot - 1)) ” &&
  “ ((pivot - 1) < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”

noncomputable def quicksort_numbers_partial_solve_wit_22_aux : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre < high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (low_pre <= pivot)) (PreH10 : (pivot <= high_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH14 : (PairedPermutation rows rows1 lens lens1)) (PreH15 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH16 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH17 : ((sum (lens1)) = (sum (lens)))) (PreH18 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= count_pre) ” &&
  “ ((-1) <= (pivot - 1)) ” &&
  “ ((pivot - 1) < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (pivot > low_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_22 : Prop := quicksort_numbers_partial_solve_wit_22_pure -> quicksort_numbers_partial_solve_wit_22_aux

noncomputable def quicksort_numbers_partial_solve_wit_23_pure : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH3 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH4 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH5 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH7 : ((sum (lens2)) = (sum (lens1)))) (PreH8 : (pivot > low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1 lens lens1)) (PreH22 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens2))) ” &&
  “ ((sum (lens2)) <= 200) ” &&
  “ (RowsWellFormed rows2 lens2 count_pre number_width_pre) ” &&
  “ (FlatRows flat2 rows2 count_pre number_width_pre) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_aux : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre)) (PreH3 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH4 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH5 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH7 : ((sum (lens2)) = (sum (lens1)))) (PreH8 : (pivot > low_pre)) (PreH9 : (1 <= count_pre)) (PreH10 : (count_pre <= 20)) (PreH11 : (1 <= number_width_pre)) (PreH12 : (number_width_pre <= 10)) (PreH13 : ((0 : Int) <= low_pre)) (PreH14 : (low_pre < high_pre)) (PreH15 : (high_pre < count_pre)) (PreH16 : (low_pre <= pivot)) (PreH17 : (pivot <= high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH21 : (PairedPermutation rows rows1 lens lens1)) (PreH22 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH23 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH24 : ((sum (lens1)) = (sum (lens)))) (PreH25 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens2))) ” &&
  “ ((sum (lens2)) <= 200) ” &&
  “ (RowsWellFormed rows2 lens2 count_pre number_width_pre) ” &&
  “ (FlatRows flat2 rows2 count_pre number_width_pre) ” &&
  “ (pivot < high_pre) ” &&
  “ (RowsWellFormed rows2 lens2 count_pre number_width_pre) ” &&
  “ (FlatRows flat2 rows2 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows1 rows2 lens1 lens2) ” &&
  “ (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1)) ” &&
  “ (GreedySortedRange rows2 lens2 low_pre (pivot - 1)) ” &&
  “ ((sum (lens2)) = (sum (lens1))) ” &&
  “ (pivot > low_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)

noncomputable def quicksort_numbers_partial_solve_wit_23 : Prop := quicksort_numbers_partial_solve_wit_23_pure -> quicksort_numbers_partial_solve_wit_23_aux

noncomputable def quicksort_numbers_partial_solve_wit_24_pure : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (low_pre <= pivot)) (PreH11 : (pivot <= high_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1 lens lens1)) (PreH16 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH17 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH18 : ((sum (lens1)) = (sum (lens)))) (PreH19 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”

noncomputable def quicksort_numbers_partial_solve_wit_24_aux : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (low_pre <= pivot)) (PreH11 : (pivot <= high_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1 lens lens1)) (PreH16 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH17 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH18 : ((sum (lens1)) = (sum (lens)))) (PreH19 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (pivot < high_pre) ” &&
  “ (pivot <= low_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_24 : Prop := quicksort_numbers_partial_solve_wit_24_pure -> quicksort_numbers_partial_solve_wit_24_aux

noncomputable def concatenating_numbers_safety_wit_1 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH8 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "result_length" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_2 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH8 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def concatenating_numbers_safety_wit_3 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH9 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((count_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (count_pre - 1)) ”

noncomputable def concatenating_numbers_safety_wit_4 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH9 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_5 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH9 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def concatenating_numbers_safety_wit_6 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (result_length : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH8 : (PairedPermutation rows rows1 lens lens1)) (PreH9 : (GreedySorted rows1 lens1)) (PreH10 : ((sum (lens1)) = (sum (lens)))) (PreH11 : (result_length = (0 : Int))) (PreH12 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.undef_full result_pre (sum (lens)))
  ** ((( &( "i" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_7 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (i : Int) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH11 : (PairedPermutation rows rows1 lens lens1)) (PreH12 : (GreedySorted rows1 lens1)) (PreH13 : ((sum (lens1)) = (sum (lens)))) (PreH14 : (output = (ConcatenatedPrefix (rows1) (lens1) (i)))) (PreH15 : (result_length = (Zlength (output)))) (PreH16 : ((0 : Int) <= result_length)) (PreH17 : (result_length <= (sum (lens)))) (PreH18 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_8 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1 lens lens1)) (PreH30 : (GreedySorted rows1 lens1)) (PreH31 : ((sum (lens1)) = (sum (lens)))) (PreH32 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "result_length" ) )) # Int |-> (result_length))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ (((i * number_width_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * number_width_pre) + j)) ”

noncomputable def concatenating_numbers_safety_wit_9 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1 lens lens1)) (PreH30 : (GreedySorted rows1 lens1)) (PreH31 : ((sum (lens1)) = (sum (lens)))) (PreH32 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "result_length" ) )) # Int |-> (result_length))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((i * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * number_width_pre)) ”

noncomputable def concatenating_numbers_safety_wit_10 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1 lens lens1)) (PreH30 : (GreedySorted rows1 lens1)) (PreH31 : ((sum (lens1)) = (sum (lens)))) (PreH32 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.seg result_pre (0 : Int) (result_length + 1) (output ++ ((Znth ((i * number_width_pre) + j) flat1 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
|--
  “ ((result_length + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result_length + 1)) ”

noncomputable def concatenating_numbers_safety_wit_11 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1 lens lens1)) (PreH30 : (GreedySorted rows1 lens1)) (PreH31 : ((sum (lens1)) = (sum (lens)))) (PreH32 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.seg result_pre (0 : Int) (result_length + 1) (output ++ ((Znth ((i * number_width_pre) + j) flat1 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "result_length" ) )) # Int |-> ((result_length + 1)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def concatenating_numbers_safety_wit_12 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= (Znth i lens1 (0 : Int)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < count_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH12 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH13 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH14 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1 lens lens1)) (PreH16 : (GreedySorted rows1 lens1)) (PreH17 : ((sum (lens1)) = (sum (lens)))) (PreH18 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : ((0 : Int) <= result_length)) (PreH21 : (result_length <= (sum (lens)))) (PreH22 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def concatenating_numbers_entail_wit_1_1 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (PreH1 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH2 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH4 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 (0 : Int) (count_pre - 1))) (PreH5 : (GreedySortedRange rows1_2 lens1_2 (0 : Int) (count_pre - 1))) (PreH6 : ((sum (lens1_2)) = (sum (lens)))) (PreH7 : (count_pre > 1)) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.undef_full result_pre (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (PreH1 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH2 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH4 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 (0 : Int) (count_pre - 1))) (PreH5 : (GreedySortedRange rows1_2 lens1_2 (0 : Int) (count_pre - 1))) (PreH6 : ((sum (lens1_2)) = (sum (lens)))) (PreH7 : (count_pre > 1)) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH15 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_1_2 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH9 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.undef_full result_pre (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH9 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens) ” &&
  “ (GreedySorted rows1 lens) ” &&
  “ (FlatRows flat rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_2 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (result_length : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH8 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH9 : (GreedySorted rows1_2 lens1_2)) (PreH10 : ((sum (lens1_2)) = (sum (lens)))) (PreH11 : (result_length = (0 : Int))) (PreH12 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  EX flat1 : (List Int), EX output : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedPrefix (rows1) (lens1) ((0 : Int)))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
) \/
(
forall (result_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (result_length : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH8 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH9 : (GreedySorted rows1_2 lens1_2)) (PreH10 : ((sum (lens1_2)) = (sum (lens)))) (PreH11 : (result_length = (0 : Int))) (PreH12 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.undef_full result_pre (sum (lens)))
|--
  EX rows1 : (List (List Int)),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ ((sum (lens1_2)) = (sum (lens))) ” &&
  “ (result_length = (Zlength ((ConcatenatedPrefix (rows1) (lens1_2) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.seg result_pre (0 : Int) result_length (ConcatenatedPrefix (rows1) (lens1_2) ((0 : Int))))
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
)

noncomputable def concatenating_numbers_entail_wit_3 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (i : Int) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH11 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH12 : (GreedySorted rows1_2 lens1_2)) (PreH13 : ((sum (lens1_2)) = (sum (lens)))) (PreH14 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH15 : (result_length = (Zlength (output_2)))) (PreH16 : ((0 : Int) <= result_length)) (PreH17 : (result_length <= (sum (lens)))) (PreH18 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX flat1 : (List Int), EX output : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) ((0 : Int)))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (i : Int) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH11 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH12 : (GreedySorted rows1_2 lens1_2)) (PreH13 : ((sum (lens1_2)) = (sum (lens)))) (PreH14 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH15 : (result_length = (Zlength (output_2)))) (PreH16 : ((0 : Int) <= result_length)) (PreH17 : (result_length <= (sum (lens)))) (PreH18 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((ConcatenatedPrefix (rows1_2) (lens1_2) (i)) = (ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Znth (i) (lens1_2) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1_2) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ ((Zlength (output_2)) = (Zlength ((ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((0 : Int)))))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_4 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1 (0 : Int)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < count_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH12 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH13 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH14 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1 lens lens1)) (PreH16 : (GreedySorted rows1 lens1)) (PreH17 : ((sum (lens1)) = (sum (lens)))) (PreH18 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : ((0 : Int) <= result_length)) (PreH21 : (result_length <= (sum (lens)))) (PreH22 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((0 : Int) <= ((i * number_width_pre) + j)) ” &&
  “ (((i * number_width_pre) + j) < (count_pre * number_width_pre)) ” &&
  “ (result_length <= INT_MAX) ” &&
  “ (result_length >= INT_MIN) ” &&
  “ (j < (Znth i lens1 (0 : Int))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (result_length <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (result_length >= INT_MIN)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (j < (Znth i lens1 (0 : Int)))) (PreH12 : (1 <= count_pre)) (PreH13 : (count_pre <= 20)) (PreH14 : (1 <= number_width_pre)) (PreH15 : (number_width_pre <= 10)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < count_pre)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH22 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH23 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH24 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH25 : (PairedPermutation rows rows1 lens lens1)) (PreH26 : (GreedySorted rows1 lens1)) (PreH27 : ((sum (lens1)) = (sum (lens)))) (PreH28 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH29 : (result_length = (Zlength (output)))) (PreH30 : ((0 : Int) <= result_length)) (PreH31 : (result_length <= (sum (lens)))) (PreH32 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (((i * number_width_pre) + j) < (count_pre * number_width_pre)) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_4_split_goal_1 : Prop :=
  forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (result_length <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (result_length >= INT_MIN)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (j < (Znth i lens1 (0 : Int)))) (PreH12 : (1 <= count_pre)) (PreH13 : (count_pre <= 20)) (PreH14 : (1 <= number_width_pre)) (PreH15 : (number_width_pre <= 10)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < count_pre)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH22 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH23 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH24 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH25 : (PairedPermutation rows rows1 lens lens1)) (PreH26 : (GreedySorted rows1 lens1)) (PreH27 : ((sum (lens1)) = (sum (lens)))) (PreH28 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH29 : (result_length = (Zlength (output)))) (PreH30 : ((0 : Int) <= result_length)) (PreH31 : (result_length <= (sum (lens)))) (PreH32 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (((i * number_width_pre) + j) < (count_pre * number_width_pre))

noncomputable def concatenating_numbers_entail_wit_5 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH2 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH3 : (result_length <= INT_MAX)) (PreH4 : (result_length >= INT_MIN)) (PreH5 : (j < (Znth i lens1 (0 : Int)))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < count_pre)) (PreH14 : ((0 : Int) <= j)) (PreH15 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH17 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH19 : (PairedPermutation rows rows1 lens lens1)) (PreH20 : (GreedySorted rows1 lens1)) (PreH21 : ((sum (lens1)) = (sum (lens)))) (PreH22 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH23 : (result_length = (Zlength (output)))) (PreH24 : ((0 : Int) <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length < (sum (lens))) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (j <= INT_MAX) ” &&
  “ (number_width_pre <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (j >= INT_MIN) ” &&
  “ (number_width_pre >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= ((i * number_width_pre) + j)) ” &&
  “ (((i * number_width_pre) + j) < (count_pre * number_width_pre)) ” &&
  “ (result_length <= INT_MAX) ” &&
  “ (result_length >= INT_MIN) ” &&
  “ (j < (Znth i lens1 (0 : Int))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  ((( &( "result_length" ) )) # Int |-> (result_length))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (count_pre <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (number_width_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (count_pre >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (number_width_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH10 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH11 : (result_length <= INT_MAX)) (PreH12 : (result_length >= INT_MIN)) (PreH13 : (j < (Znth i lens1 (0 : Int)))) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < count_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH24 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH25 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH26 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH27 : (PairedPermutation rows rows1 lens lens1)) (PreH28 : (GreedySorted rows1 lens1)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH31 : (result_length = (Zlength (output)))) (PreH32 : ((0 : Int) <= result_length)) (PreH33 : (result_length <= (sum (lens)))) (PreH34 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  “ (result_length < (sum (lens))) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_5_split_goal_1 : Prop :=
  forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (count_pre <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (number_width_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (count_pre >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (number_width_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH10 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH11 : (result_length <= INT_MAX)) (PreH12 : (result_length >= INT_MIN)) (PreH13 : (j < (Znth i lens1 (0 : Int)))) (PreH14 : (1 <= count_pre)) (PreH15 : (count_pre <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < count_pre)) (PreH22 : ((0 : Int) <= j)) (PreH23 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH24 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH25 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH26 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH27 : (PairedPermutation rows rows1 lens lens1)) (PreH28 : (GreedySorted rows1 lens1)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH31 : (result_length = (Zlength (output)))) (PreH32 : ((0 : Int) <= result_length)) (PreH33 : (result_length <= (sum (lens)))) (PreH34 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (result_length < (sum (lens)))

noncomputable def concatenating_numbers_entail_wit_6 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1_2 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH30 : (GreedySorted rows1_2 lens1_2)) (PreH31 : ((sum (lens1_2)) = (sum (lens)))) (PreH32 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH33 : (result_length = (Zlength (output_2)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.seg result_pre (0 : Int) (result_length + 1) (output_2 ++ ((Znth ((i * number_width_pre) + j) flat1_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX output : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) ((j + 1)))) ” &&
  “ ((result_length + 1) = (Zlength (output))) ” &&
  “ ((0 : Int) <= (result_length + 1)) ” &&
  “ ((result_length + 1) <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) (result_length + 1) output)
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1_2 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH30 : (GreedySorted rows1_2 lens1_2)) (PreH31 : ((sum (lens1_2)) = (sum (lens)))) (PreH32 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH33 : (result_length = (Zlength (output_2)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (((ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)) ++ ((Znth ((i * number_width_pre) + j) flat1_2 (0 : Int)) :: (@List.nil Int))) = (ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((j + 1)))) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (Znth (i) (lens1_2) ((0 : Int)))) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ (((Zlength (output_2)) + 1) = (Zlength ((ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((j + 1)))))) ” &&
  “ ((0 : Int) <= ((Zlength (output_2)) + 1)) ” &&
  “ (((Zlength (output_2)) + 1) <= (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_7 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= (Znth i lens1_2 (0 : Int)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < count_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH12 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH13 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH14 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH16 : (GreedySorted rows1_2 lens1_2)) (PreH17 : ((sum (lens1_2)) = (sum (lens)))) (PreH18 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : ((0 : Int) <= result_length)) (PreH21 : (result_length <= (sum (lens)))) (PreH22 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX flat1 : (List Int), EX output : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= count_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedPrefix (rows1) (lens1) ((i + 1)))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= (Znth i lens1_2 (0 : Int)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < count_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH12 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH13 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH14 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH15 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH16 : (GreedySorted rows1_2 lens1_2)) (PreH17 : ((sum (lens1_2)) = (sum (lens)))) (PreH18 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : ((0 : Int) <= result_length)) (PreH21 : (result_length <= (sum (lens)))) (PreH22 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)) = (ConcatenatedPrefix (rows1) (lens1_2) ((i + 1)))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= count_pre) ” &&
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ ((Zlength (output_2)) = (Zlength ((ConcatenatedPrefix (rows1) (lens1_2) ((i + 1)))))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_return_wit_1 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (i : Int) (PreH1 : (i >= count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH11 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH12 : (GreedySorted rows1_2 lens1_2)) (PreH13 : ((sum (lens1_2)) = (sum (lens)))) (PreH14 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH15 : (result_length = (Zlength (output_2)))) (PreH16 : ((0 : Int) <= result_length)) (PreH17 : (result_length <= (sum (lens)))) (PreH18 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX output : (List Int), EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ (result_pre = result_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (LargestConcatenation rows rows1 lens lens1 output) ” &&
  “ ((Zlength (output)) = (sum (lens))) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full result_pre (sum (lens)) output)
) \/
(
forall (result_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (i : Int) (PreH1 : (i >= count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre)) (PreH11 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH12 : (GreedySorted rows1_2 lens1_2)) (PreH13 : ((sum (lens1_2)) = (sum (lens)))) (PreH14 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH15 : (result_length = (Zlength (output_2)))) (PreH16 : ((0 : Int) <= result_length)) (PreH17 : (result_length <= (sum (lens)))) (PreH18 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX output : (List Int), EX rows1 : (List (List Int)),
  “ (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ” &&
  “ (LargestConcatenation rows rows1 lens lens1_2 output) ” &&
  “ ((Zlength (output)) = (sum (lens))) ”
  &&  (intArray.full result_pre (sum (lens)) output)
)

noncomputable def concatenating_numbers_partial_solve_wit_1_pure : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH9 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ ((-1) <= (count_pre - 1)) ” &&
  “ ((count_pre - 1) < count_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows lens count_pre number_width_pre) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ”

noncomputable def concatenating_numbers_partial_solve_wit_1_aux : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH9 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ ((-1) <= (count_pre - 1)) ” &&
  “ ((count_pre - 1) < count_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows lens count_pre number_width_pre) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ” &&
  “ (count_pre > 1) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (RowsWellFormed rows lens count_pre number_width_pre) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))

noncomputable def concatenating_numbers_partial_solve_wit_1 : Prop := concatenating_numbers_partial_solve_wit_1_pure -> concatenating_numbers_partial_solve_wit_1_aux

noncomputable def concatenating_numbers_partial_solve_wit_2 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < count_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH11 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH12 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH13 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH14 : (PairedPermutation rows rows1 lens lens1)) (PreH15 : (GreedySorted rows1 lens1)) (PreH16 : ((sum (lens1)) = (sum (lens)))) (PreH17 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH18 : (result_length = (Zlength (output)))) (PreH19 : ((0 : Int) <= result_length)) (PreH20 : (result_length <= (sum (lens)))) (PreH21 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((lengths_pre + (i * sizeof(INT)))) # Int |-> ((Znth i lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre i (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))

noncomputable def concatenating_numbers_partial_solve_wit_3 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1 lens lens1)) (PreH30 : (GreedySorted rows1 lens1)) (PreH31 : ((sum (lens1)) = (sum (lens)))) (PreH32 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length < (sum (lens))) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (j <= INT_MAX) ” &&
  “ (number_width_pre <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (j >= INT_MIN) ” &&
  “ (number_width_pre >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= ((i * number_width_pre) + j)) ” &&
  “ (((i * number_width_pre) + j) < (count_pre * number_width_pre)) ” &&
  “ (result_length <= INT_MAX) ” &&
  “ (result_length >= INT_MIN) ” &&
  “ (j < (Znth i lens1 (0 : Int))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((i * number_width_pre) + j) * sizeof(INT)))) # Int |-> ((Znth ((i * number_width_pre) + j) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((i * number_width_pre) + j) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))

noncomputable def concatenating_numbers_partial_solve_wit_4 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : ((0 : Int) <= ((i * number_width_pre) + j))) (PreH12 : (((i * number_width_pre) + j) < (count_pre * number_width_pre))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (result_length >= INT_MIN)) (PreH15 : (j < (Znth i lens1 (0 : Int)))) (PreH16 : (1 <= count_pre)) (PreH17 : (count_pre <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < count_pre)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH26 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH27 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH28 : (RowsWellFormed rows1 lens1 count_pre number_width_pre)) (PreH29 : (PairedPermutation rows rows1 lens lens1)) (PreH30 : (GreedySorted rows1 lens1)) (PreH31 : ((sum (lens1)) = (sum (lens)))) (PreH32 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : (result_length <= (sum (lens)))) (PreH36 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length < (sum (lens))) ” &&
  “ (count_pre <= INT_MAX) ” &&
  “ (j <= INT_MAX) ” &&
  “ (number_width_pre <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (count_pre >= INT_MIN) ” &&
  “ (j >= INT_MIN) ” &&
  “ (number_width_pre >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= ((i * number_width_pre) + j)) ” &&
  “ (((i * number_width_pre) + j) < (count_pre * number_width_pre)) ” &&
  “ (result_length <= INT_MAX) ” &&
  “ (result_length >= INT_MIN) ” &&
  “ (j < (Znth i lens1 (0 : Int))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ (RowsWellFormed rows1 lens1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((result_pre + (result_length * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)


structure VC_Correct : Type where
  proof_of_quicksort_numbers_safety_wit_1 : quicksort_numbers_safety_wit_1
  proof_of_quicksort_numbers_safety_wit_2 : quicksort_numbers_safety_wit_2
  proof_of_quicksort_numbers_safety_wit_3 : quicksort_numbers_safety_wit_3
  proof_of_quicksort_numbers_safety_wit_4 : quicksort_numbers_safety_wit_4
  proof_of_quicksort_numbers_safety_wit_5 : quicksort_numbers_safety_wit_5
  proof_of_quicksort_numbers_safety_wit_7 : quicksort_numbers_safety_wit_7
  proof_of_quicksort_numbers_safety_wit_8 : quicksort_numbers_safety_wit_8
  proof_of_quicksort_numbers_safety_wit_9 : quicksort_numbers_safety_wit_9
  proof_of_quicksort_numbers_safety_wit_10 : quicksort_numbers_safety_wit_10
  proof_of_quicksort_numbers_safety_wit_11 : quicksort_numbers_safety_wit_11
  proof_of_quicksort_numbers_safety_wit_12 : quicksort_numbers_safety_wit_12
  proof_of_quicksort_numbers_safety_wit_13 : quicksort_numbers_safety_wit_13
  proof_of_quicksort_numbers_safety_wit_14 : quicksort_numbers_safety_wit_14
  proof_of_quicksort_numbers_safety_wit_15 : quicksort_numbers_safety_wit_15
  proof_of_quicksort_numbers_safety_wit_16 : quicksort_numbers_safety_wit_16
  proof_of_quicksort_numbers_safety_wit_17 : quicksort_numbers_safety_wit_17
  proof_of_quicksort_numbers_safety_wit_18 : quicksort_numbers_safety_wit_18
  proof_of_quicksort_numbers_safety_wit_20 : quicksort_numbers_safety_wit_20
  proof_of_quicksort_numbers_safety_wit_21 : quicksort_numbers_safety_wit_21
  proof_of_quicksort_numbers_safety_wit_22 : quicksort_numbers_safety_wit_22
  proof_of_quicksort_numbers_safety_wit_23 : quicksort_numbers_safety_wit_23
  proof_of_quicksort_numbers_safety_wit_24 : quicksort_numbers_safety_wit_24
  proof_of_quicksort_numbers_safety_wit_25 : quicksort_numbers_safety_wit_25
  proof_of_quicksort_numbers_safety_wit_26 : quicksort_numbers_safety_wit_26
  proof_of_quicksort_numbers_safety_wit_27 : quicksort_numbers_safety_wit_27
  proof_of_quicksort_numbers_safety_wit_28 : quicksort_numbers_safety_wit_28
  proof_of_quicksort_numbers_safety_wit_29 : quicksort_numbers_safety_wit_29
  proof_of_quicksort_numbers_safety_wit_30 : quicksort_numbers_safety_wit_30
  proof_of_quicksort_numbers_safety_wit_31 : quicksort_numbers_safety_wit_31
  proof_of_quicksort_numbers_safety_wit_32 : quicksort_numbers_safety_wit_32
  proof_of_quicksort_numbers_safety_wit_33 : quicksort_numbers_safety_wit_33
  proof_of_quicksort_numbers_safety_wit_34 : quicksort_numbers_safety_wit_34
  proof_of_quicksort_numbers_safety_wit_35 : quicksort_numbers_safety_wit_35
  proof_of_quicksort_numbers_safety_wit_36 : quicksort_numbers_safety_wit_36
  proof_of_quicksort_numbers_safety_wit_37 : quicksort_numbers_safety_wit_37
  proof_of_quicksort_numbers_safety_wit_38 : quicksort_numbers_safety_wit_38
  proof_of_quicksort_numbers_safety_wit_39 : quicksort_numbers_safety_wit_39
  proof_of_quicksort_numbers_safety_wit_40 : quicksort_numbers_safety_wit_40
  proof_of_quicksort_numbers_safety_wit_41 : quicksort_numbers_safety_wit_41
  proof_of_quicksort_numbers_safety_wit_42 : quicksort_numbers_safety_wit_42
  proof_of_quicksort_numbers_safety_wit_43 : quicksort_numbers_safety_wit_43
  proof_of_quicksort_numbers_safety_wit_44 : quicksort_numbers_safety_wit_44
  proof_of_quicksort_numbers_safety_wit_45 : quicksort_numbers_safety_wit_45
  proof_of_quicksort_numbers_safety_wit_46 : quicksort_numbers_safety_wit_46
  proof_of_quicksort_numbers_safety_wit_47 : quicksort_numbers_safety_wit_47
  proof_of_quicksort_numbers_safety_wit_48 : quicksort_numbers_safety_wit_48
  proof_of_quicksort_numbers_safety_wit_49 : quicksort_numbers_safety_wit_49
  proof_of_quicksort_numbers_safety_wit_50 : quicksort_numbers_safety_wit_50
  proof_of_quicksort_numbers_safety_wit_51 : quicksort_numbers_safety_wit_51
  proof_of_quicksort_numbers_safety_wit_52 : quicksort_numbers_safety_wit_52
  proof_of_quicksort_numbers_entail_wit_3 : quicksort_numbers_entail_wit_3
  proof_of_quicksort_numbers_entail_wit_5 : quicksort_numbers_entail_wit_5
  proof_of_quicksort_numbers_entail_wit_8 : quicksort_numbers_entail_wit_8
  proof_of_quicksort_numbers_entail_wit_10 : quicksort_numbers_entail_wit_10
  proof_of_quicksort_numbers_partial_solve_wit_1 : quicksort_numbers_partial_solve_wit_1
  proof_of_quicksort_numbers_partial_solve_wit_2 : quicksort_numbers_partial_solve_wit_2
  proof_of_quicksort_numbers_partial_solve_wit_3 : quicksort_numbers_partial_solve_wit_3
  proof_of_quicksort_numbers_partial_solve_wit_4 : quicksort_numbers_partial_solve_wit_4
  proof_of_quicksort_numbers_partial_solve_wit_5 : quicksort_numbers_partial_solve_wit_5
  proof_of_quicksort_numbers_partial_solve_wit_6 : quicksort_numbers_partial_solve_wit_6
  proof_of_quicksort_numbers_partial_solve_wit_7 : quicksort_numbers_partial_solve_wit_7
  proof_of_quicksort_numbers_partial_solve_wit_8 : quicksort_numbers_partial_solve_wit_8
  proof_of_quicksort_numbers_partial_solve_wit_9 : quicksort_numbers_partial_solve_wit_9
  proof_of_quicksort_numbers_partial_solve_wit_10 : quicksort_numbers_partial_solve_wit_10
  proof_of_quicksort_numbers_partial_solve_wit_11 : quicksort_numbers_partial_solve_wit_11
  proof_of_quicksort_numbers_partial_solve_wit_12 : quicksort_numbers_partial_solve_wit_12
  proof_of_quicksort_numbers_partial_solve_wit_13 : quicksort_numbers_partial_solve_wit_13
  proof_of_quicksort_numbers_partial_solve_wit_14 : quicksort_numbers_partial_solve_wit_14
  proof_of_quicksort_numbers_partial_solve_wit_15 : quicksort_numbers_partial_solve_wit_15
  proof_of_quicksort_numbers_partial_solve_wit_16 : quicksort_numbers_partial_solve_wit_16
  proof_of_quicksort_numbers_partial_solve_wit_17 : quicksort_numbers_partial_solve_wit_17
  proof_of_quicksort_numbers_partial_solve_wit_18 : quicksort_numbers_partial_solve_wit_18
  proof_of_quicksort_numbers_partial_solve_wit_19 : quicksort_numbers_partial_solve_wit_19
  proof_of_quicksort_numbers_partial_solve_wit_20 : quicksort_numbers_partial_solve_wit_20
  proof_of_quicksort_numbers_partial_solve_wit_21 : quicksort_numbers_partial_solve_wit_21
  proof_of_quicksort_numbers_partial_solve_wit_22_pure : quicksort_numbers_partial_solve_wit_22_pure
  proof_of_quicksort_numbers_partial_solve_wit_22 : quicksort_numbers_partial_solve_wit_22
  proof_of_quicksort_numbers_partial_solve_wit_23_pure : quicksort_numbers_partial_solve_wit_23_pure
  proof_of_quicksort_numbers_partial_solve_wit_23 : quicksort_numbers_partial_solve_wit_23
  proof_of_quicksort_numbers_partial_solve_wit_24_pure : quicksort_numbers_partial_solve_wit_24_pure
  proof_of_quicksort_numbers_partial_solve_wit_24 : quicksort_numbers_partial_solve_wit_24
  proof_of_concatenating_numbers_safety_wit_1 : concatenating_numbers_safety_wit_1
  proof_of_concatenating_numbers_safety_wit_2 : concatenating_numbers_safety_wit_2
  proof_of_concatenating_numbers_safety_wit_3 : concatenating_numbers_safety_wit_3
  proof_of_concatenating_numbers_safety_wit_4 : concatenating_numbers_safety_wit_4
  proof_of_concatenating_numbers_safety_wit_5 : concatenating_numbers_safety_wit_5
  proof_of_concatenating_numbers_safety_wit_6 : concatenating_numbers_safety_wit_6
  proof_of_concatenating_numbers_safety_wit_7 : concatenating_numbers_safety_wit_7
  proof_of_concatenating_numbers_safety_wit_8 : concatenating_numbers_safety_wit_8
  proof_of_concatenating_numbers_safety_wit_9 : concatenating_numbers_safety_wit_9
  proof_of_concatenating_numbers_safety_wit_10 : concatenating_numbers_safety_wit_10
  proof_of_concatenating_numbers_safety_wit_11 : concatenating_numbers_safety_wit_11
  proof_of_concatenating_numbers_safety_wit_12 : concatenating_numbers_safety_wit_12
  proof_of_concatenating_numbers_partial_solve_wit_1_pure : concatenating_numbers_partial_solve_wit_1_pure
  proof_of_concatenating_numbers_partial_solve_wit_1 : concatenating_numbers_partial_solve_wit_1
  proof_of_concatenating_numbers_partial_solve_wit_2 : concatenating_numbers_partial_solve_wit_2
  proof_of_concatenating_numbers_partial_solve_wit_3 : concatenating_numbers_partial_solve_wit_3
  proof_of_concatenating_numbers_partial_solve_wit_4 : concatenating_numbers_partial_solve_wit_4
  proof_of_quicksort_numbers_safety_wit_6 : quicksort_numbers_safety_wit_6
  proof_of_quicksort_numbers_safety_wit_19 : quicksort_numbers_safety_wit_19
  proof_of_quicksort_numbers_entail_wit_1 : quicksort_numbers_entail_wit_1
  proof_of_quicksort_numbers_entail_wit_2 : quicksort_numbers_entail_wit_2
  proof_of_quicksort_numbers_entail_wit_4 : quicksort_numbers_entail_wit_4
  proof_of_quicksort_numbers_entail_wit_6 : quicksort_numbers_entail_wit_6
  proof_of_quicksort_numbers_entail_wit_7_1 : quicksort_numbers_entail_wit_7_1
  proof_of_quicksort_numbers_entail_wit_7_2 : quicksort_numbers_entail_wit_7_2
  proof_of_quicksort_numbers_entail_wit_9 : quicksort_numbers_entail_wit_9
  proof_of_quicksort_numbers_entail_wit_11 : quicksort_numbers_entail_wit_11
  proof_of_quicksort_numbers_entail_wit_12_1 : quicksort_numbers_entail_wit_12_1
  proof_of_quicksort_numbers_entail_wit_12_2 : quicksort_numbers_entail_wit_12_2
  proof_of_quicksort_numbers_entail_wit_13 : quicksort_numbers_entail_wit_13
  proof_of_quicksort_numbers_entail_wit_14_1 : quicksort_numbers_entail_wit_14_1
  proof_of_quicksort_numbers_entail_wit_14_2 : quicksort_numbers_entail_wit_14_2
  proof_of_quicksort_numbers_entail_wit_15 : quicksort_numbers_entail_wit_15
  proof_of_quicksort_numbers_entail_wit_16 : quicksort_numbers_entail_wit_16
  proof_of_quicksort_numbers_entail_wit_17 : quicksort_numbers_entail_wit_17
  proof_of_quicksort_numbers_entail_wit_18 : quicksort_numbers_entail_wit_18
  proof_of_quicksort_numbers_entail_wit_19_1 : quicksort_numbers_entail_wit_19_1
  proof_of_quicksort_numbers_entail_wit_19_2 : quicksort_numbers_entail_wit_19_2
  proof_of_quicksort_numbers_entail_wit_20 : quicksort_numbers_entail_wit_20
  proof_of_quicksort_numbers_entail_wit_21 : quicksort_numbers_entail_wit_21
  proof_of_quicksort_numbers_entail_wit_22 : quicksort_numbers_entail_wit_22
  proof_of_quicksort_numbers_entail_wit_23 : quicksort_numbers_entail_wit_23
  proof_of_quicksort_numbers_entail_wit_24 : quicksort_numbers_entail_wit_24
  proof_of_quicksort_numbers_entail_wit_25 : quicksort_numbers_entail_wit_25
  proof_of_quicksort_numbers_return_wit_1 : quicksort_numbers_return_wit_1
  proof_of_quicksort_numbers_return_wit_2 : quicksort_numbers_return_wit_2
  proof_of_quicksort_numbers_return_wit_3 : quicksort_numbers_return_wit_3
  proof_of_quicksort_numbers_return_wit_4 : quicksort_numbers_return_wit_4
  proof_of_concatenating_numbers_entail_wit_1_1 : concatenating_numbers_entail_wit_1_1
  proof_of_concatenating_numbers_entail_wit_1_2 : concatenating_numbers_entail_wit_1_2
  proof_of_concatenating_numbers_entail_wit_2 : concatenating_numbers_entail_wit_2
  proof_of_concatenating_numbers_entail_wit_3 : concatenating_numbers_entail_wit_3
  proof_of_concatenating_numbers_entail_wit_4 : concatenating_numbers_entail_wit_4
  proof_of_concatenating_numbers_entail_wit_5 : concatenating_numbers_entail_wit_5
  proof_of_concatenating_numbers_entail_wit_6 : concatenating_numbers_entail_wit_6
  proof_of_concatenating_numbers_entail_wit_7 : concatenating_numbers_entail_wit_7
  proof_of_concatenating_numbers_return_wit_1 : concatenating_numbers_return_wit_1

end Algorithms.concatenating_numbers.lean.groundtruth.concatenating_numbers_goal
