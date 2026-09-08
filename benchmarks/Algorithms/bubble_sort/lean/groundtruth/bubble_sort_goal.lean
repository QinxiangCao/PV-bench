import SimpleC.SL.SeparationLogic

import Algorithms.bubble_sort.lean.helper_lib
open AUXLib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.bubble_sort.lean.groundtruth.bubble_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bubble_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def sortArray_safety_wit_1 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_2 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : (numsSize_pre > 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sortArray_safety_wit_3 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = (l1 ++ l2))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l2)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (1 <= (Zlength (l1)))) (PreH9 : (Permutation l l3)) (PreH10 : (Sorting.increasing l2)) (PreH11 : (prefix_suffix_sorted l1 l2)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ ((numsSize_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numsSize_pre - 1)) ”

noncomputable def sortArray_safety_wit_4 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = (l1 ++ l2))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l2)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (1 <= (Zlength (l1)))) (PreH9 : (Permutation l l3)) (PreH10 : (Sorting.increasing l2)) (PreH11 : (prefix_suffix_sorted l1 l2)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_5 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (PreH1 : (i < (numsSize_pre - 1))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (l1 ++ l2))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1)))) (PreH10 : (Permutation l l3)) (PreH11 : (Sorting.increasing l2)) (PreH12 : (prefix_suffix_sorted l1 l2)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sortArray_safety_wit_6 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l4)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (i < (numsSize_pre - 1))) (PreH9 : (j = (Zlength (l1)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : ((j + 1) <= (numsSize_pre - i))) (PreH12 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH13 : (Permutation l l3)) (PreH14 : (Sorting.increasing l4)) (PreH15 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH16 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ ((numsSize_pre - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (numsSize_pre - i)) ”

noncomputable def sortArray_safety_wit_7 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l4)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (i < (numsSize_pre - 1))) (PreH9 : (j = (Zlength (l1)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : ((j + 1) <= (numsSize_pre - i))) (PreH12 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH13 : (Permutation l l3)) (PreH14 : (Sorting.increasing l4)) (PreH15 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH16 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_8 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l4)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (i < (numsSize_pre - 1))) (PreH9 : (j = (Zlength (l1)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : ((j + 1) <= (numsSize_pre - i))) (PreH12 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH13 : (Permutation l l3)) (PreH14 : (Sorting.increasing l4)) (PreH15 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH16 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_9 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((j + 1) < (numsSize_pre - i))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : ((j + 1) <= (numsSize_pre - i))) (PreH13 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH14 : (Permutation l l3)) (PreH15 : (Sorting.increasing l4)) (PreH16 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH17 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_10 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((j + 1) < (numsSize_pre - i))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : ((j + 1) <= (numsSize_pre - i))) (PreH13 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH14 : (Permutation l l3)) (PreH15 : (Sorting.increasing l4)) (PreH16 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH17 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_11 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j l3 (0 : Int))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_12 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j l3 (0 : Int))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_13 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1) l3 (0 : Int))) (l3)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j l3 (0 : Int))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_14 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1) l3 (0 : Int))) (l3)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j l3 (0 : Int))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_15 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) ((Znth j l3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) l3 (0 : Int))) (l3)))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_16 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) <= (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_17 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((j + 1) >= (numsSize_pre - i))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : ((j + 1) <= (numsSize_pre - i))) (PreH13 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH14 : (Permutation l l3)) (PreH15 : (Sorting.increasing l4)) (PreH16 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH17 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sortArray_entail_wit_1 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : (numsSize_pre > 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l1 : (List Int), EX l2 : (List Int), EX l3 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = (l1 ++ l2)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ ((0 : Int) = (Zlength (l2))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < numsSize_pre) ” &&
  “ (1 <= (Zlength (l1))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l2) ” &&
  “ (prefix_suffix_sorted l1 l2) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (PreH1 : (numsSize_pre > 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((Zlength (l)) = (Zlength (l))) ” &&
  “ ((0 : Int) = (Zlength (l2))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (Zlength (l))) ” &&
  “ (1 <= (Zlength (l1))) ” &&
  “ (Permutation l (l1 ++ l2)) ” &&
  “ (Sorting.increasing l2) ” &&
  “ (prefix_suffix_sorted l1 l2) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_2 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (PreH1 : (i < (numsSize_pre - 1))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (l1_2 ++ l2_2))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2_2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3_2)) (PreH11 : (Sorting.increasing l2_2)) (PreH12 : (prefix_suffix_sorted l1_2 l2_2)) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3_2)
|--
  EX l1 : (List Int), EX key : Int, EX l2 : (List Int), EX l4 : (List Int), EX l3 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ ((0 : Int) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (((0 : Int) + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (PreH1 : (i < (numsSize_pre - 1))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (l1_2 ++ l2_2))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2_2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3_2)) (PreH11 : (Sorting.increasing l2_2)) (PreH12 : (prefix_suffix_sorted l1_2 l2_2)) ,
  TT && emp 
|--
  EX l1 : (List Int), EX key : Int, EX l2 : (List Int), EX l4 : (List Int),
  “ ((l1_2 ++ l2_2) = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ ((Zlength (l2_2)) = (Zlength (l4))) ” &&
  “ ((0 : Int) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (((0 : Int) + 1) <= ((Zlength (l)) - (Zlength (l2_2)))) ” &&
  “ (((Zlength (l)) - (Zlength (l2_2))) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_3_1 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1_2 : (List Int)) (key_2 : Int) (l2_2 : (List Int)) (l4_2 : (List Int)) (l3_2 : (List Int)) (PreH1 : ((Znth j l3_2 (0 : Int)) > (Znth (j + 1) l3_2 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = ((l1_2 ++ (key_2 :: l2_2)) ++ l4_2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1_2 ++ (key_2 :: l2_2)))))) (PreH15 : (Permutation l l3_2)) (PreH16 : (Sorting.increasing l4_2)) (PreH17 : (prefix_suffix_sorted (l1_2 ++ (key_2 :: l2_2)) l4_2)) (PreH18 : (prefix_suffix_sorted l1_2 (key_2 :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) ((Znth j l3_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) l3_2 (0 : Int))) (l3_2)))))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l1 : (List Int), EX key : Int, EX l2 : (List Int), EX l4 : (List Int), EX l3 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ ((j + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ (((j + 1) + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1_2 : (List Int)) (key_2 : Int) (l2_2 : (List Int)) (l4_2 : (List Int)) (l3_2 : (List Int)) (PreH1 : ((Znth j l3_2 (0 : Int)) > (Znth (j + 1) l3_2 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = ((l1_2 ++ (key_2 :: l2_2)) ++ l4_2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1_2 ++ (key_2 :: l2_2)))))) (PreH15 : (Permutation l l3_2)) (PreH16 : (Sorting.increasing l4_2)) (PreH17 : (prefix_suffix_sorted (l1_2 ++ (key_2 :: l2_2)) l4_2)) (PreH18 : (prefix_suffix_sorted l1_2 (key_2 :: (@List.nil Int)))) ,
  TT && emp 
|--
  EX l1 : (List Int), EX key : Int, EX l2 : (List Int), EX l4 : (List Int),
  “ ((replace_Znth (((Zlength (l1_2)) + 1)) ((Znth (Zlength (l1_2)) ((l1_2 ++ (key_2 :: l2_2)) ++ l4_2) (0 : Int))) ((replace_Znth ((Zlength (l1_2))) ((Znth ((Zlength (l1_2)) + 1) ((l1_2 ++ (key_2 :: l2_2)) ++ l4_2) (0 : Int))) (((l1_2 ++ (key_2 :: l2_2)) ++ l4_2))))) = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ ((Zlength (l4_2)) = (Zlength (l4))) ” &&
  “ (((Zlength (l1_2)) + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= ((Zlength (l1_2)) + 1)) ” &&
  “ ((((Zlength (l1_2)) + 1) + 1) <= ((Zlength (l)) - (Zlength (l4_2)))) ” &&
  “ (((Zlength (l)) - (Zlength (l4_2))) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_3_2 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1_2 : (List Int)) (key_2 : Int) (l2_2 : (List Int)) (l4_2 : (List Int)) (l3_2 : (List Int)) (PreH1 : ((Znth j l3_2 (0 : Int)) <= (Znth (j + 1) l3_2 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = ((l1_2 ++ (key_2 :: l2_2)) ++ l4_2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1_2 ++ (key_2 :: l2_2)))))) (PreH15 : (Permutation l l3_2)) (PreH16 : (Sorting.increasing l4_2)) (PreH17 : (prefix_suffix_sorted (l1_2 ++ (key_2 :: l2_2)) l4_2)) (PreH18 : (prefix_suffix_sorted l1_2 (key_2 :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3_2)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l1 : (List Int), EX key : Int, EX l2 : (List Int), EX l4 : (List Int), EX l3 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ ((j + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ (((j + 1) + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1_2 : (List Int)) (key_2 : Int) (l2_2 : (List Int)) (l4_2 : (List Int)) (l3_2 : (List Int)) (PreH1 : ((Znth j l3_2 (0 : Int)) <= (Znth (j + 1) l3_2 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = ((l1_2 ++ (key_2 :: l2_2)) ++ l4_2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1_2 ++ (key_2 :: l2_2)))))) (PreH15 : (Permutation l l3_2)) (PreH16 : (Sorting.increasing l4_2)) (PreH17 : (prefix_suffix_sorted (l1_2 ++ (key_2 :: l2_2)) l4_2)) (PreH18 : (prefix_suffix_sorted l1_2 (key_2 :: (@List.nil Int)))) ,
  TT && emp 
|--
  EX l1 : (List Int), EX key : Int, EX l2 : (List Int), EX l4 : (List Int),
  “ (((l1_2 ++ (key_2 :: l2_2)) ++ l4_2) = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ ((Zlength (l4_2)) = (Zlength (l4))) ” &&
  “ (((Zlength (l1_2)) + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= ((Zlength (l1_2)) + 1)) ” &&
  “ ((((Zlength (l1_2)) + 1) + 1) <= ((Zlength (l)) - (Zlength (l4_2)))) ” &&
  “ (((Zlength (l)) - (Zlength (l4_2))) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_4 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1_2 : (List Int)) (key : Int) (l2_2 : (List Int)) (l4 : (List Int)) (l3_2 : (List Int)) (PreH1 : ((j + 1) >= (numsSize_pre - i))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = ((l1_2 ++ (key :: l2_2)) ++ l4))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1))) (PreH10 : (j = (Zlength (l1_2)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : ((j + 1) <= (numsSize_pre - i))) (PreH13 : ((numsSize_pre - i) = (Zlength ((l1_2 ++ (key :: l2_2)))))) (PreH14 : (Permutation l l3_2)) (PreH15 : (Sorting.increasing l4)) (PreH16 : (prefix_suffix_sorted (l1_2 ++ (key :: l2_2)) l4)) (PreH17 : (prefix_suffix_sorted l1_2 (key :: (@List.nil Int)))) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3_2)
|--
  EX l1 : (List Int), EX l2 : (List Int), EX l3 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = (l1 ++ l2)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ ((i + 1) = (Zlength (l2))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < numsSize_pre) ” &&
  “ (1 <= (Zlength (l1))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l2) ” &&
  “ (prefix_suffix_sorted l1 l2) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1_2 : (List Int)) (key : Int) (l2_2 : (List Int)) (l4 : (List Int)) (l3_2 : (List Int)) (PreH1 : ((j + 1) >= (numsSize_pre - i))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = ((l1_2 ++ (key :: l2_2)) ++ l4))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1))) (PreH10 : (j = (Zlength (l1_2)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : ((j + 1) <= (numsSize_pre - i))) (PreH13 : ((numsSize_pre - i) = (Zlength ((l1_2 ++ (key :: l2_2)))))) (PreH14 : (Permutation l l3_2)) (PreH15 : (Sorting.increasing l4)) (PreH16 : (prefix_suffix_sorted (l1_2 ++ (key :: l2_2)) l4)) (PreH17 : (prefix_suffix_sorted l1_2 (key :: (@List.nil Int)))) ,
  TT && emp 
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (((l1_2 ++ (key :: l2_2)) ++ l4) = (l1 ++ l2)) ” &&
  “ (((Zlength (l4)) + 1) = (Zlength (l2))) ” &&
  “ ((0 : Int) <= ((Zlength (l4)) + 1)) ” &&
  “ (((Zlength (l4)) + 1) < (Zlength (l))) ” &&
  “ (1 <= (Zlength (l1))) ” &&
  “ (Permutation l (l1 ++ l2)) ” &&
  “ (Sorting.increasing l2) ” &&
  “ (prefix_suffix_sorted l1 l2) ”
  &&  emp
)

noncomputable def sortArray_return_wit_1 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l1_2 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (PreH1 : (i >= (numsSize_pre - 1))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (l1_2 ++ l2))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3)) (PreH11 : (Sorting.increasing l2)) (PreH12 : (prefix_suffix_sorted l1_2 l2)) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (Sorting.increasing l1) ” &&
  “ ((Zlength (l1)) = numsSize_pre) ”
  &&  (intArray.full nums_pre numsSize_pre l1)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l1_2 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (PreH1 : (i >= (numsSize_pre - 1))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (l1_2 ++ l2))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3)) (PreH11 : (Sorting.increasing l2)) (PreH12 : (prefix_suffix_sorted l1_2 l2)) ,
  TT && emp 
|--
  “ ((Zlength (l3)) = numsSize_pre) ” &&
  “ (Sorting.increasing l3) ”
  &&  emp
)

noncomputable def sortArray_return_wit_1_split_goal_1 : Prop :=
  forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l1_2 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (PreH1 : (i >= (numsSize_pre - 1))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (l1_2 ++ l2))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3)) (PreH11 : (Sorting.increasing l2)) (PreH12 : (prefix_suffix_sorted l1_2 l2)) ,
  ((Zlength (l3)) = numsSize_pre)

noncomputable def sortArray_return_wit_1_split_goal_2 : Prop :=
  forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l1_2 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (PreH1 : (i >= (numsSize_pre - 1))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (l1_2 ++ l2))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3)) (PreH11 : (Sorting.increasing l2)) (PreH12 : (prefix_suffix_sorted l1_2 l2)) ,
  (Sorting.increasing l3)

noncomputable def sortArray_return_wit_2 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (Sorting.increasing l1) ” &&
  “ ((Zlength (l1)) = numsSize_pre) ”
  &&  (intArray.full nums_pre numsSize_pre l1)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  “ (Sorting.increasing l) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def sortArray_return_wit_2_split_goal_1 : Prop :=
  forall (numsSize_pre : Int) (l : (List Int)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (Sorting.increasing l)

noncomputable def sortArray_return_wit_2_split_goal_2 : Prop :=
  forall (numsSize_pre : Int) (l : (List Int)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (Permutation l l)

noncomputable def sortArray_partial_solve_wit_1 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((j + 1) < (numsSize_pre - i))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : ((j + 1) <= (numsSize_pre - i))) (PreH13 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH14 : (Permutation l l3)) (PreH15 : (Sorting.increasing l4)) (PreH16 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH17 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ ((j + 1) < (numsSize_pre - i)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ (j = (Zlength (l1))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ ((j + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |-> ((Znth j l3 (0 : Int))))
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_2 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((j + 1) < (numsSize_pre - i))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : ((j + 1) <= (numsSize_pre - i))) (PreH13 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH14 : (Permutation l l3)) (PreH15 : (Sorting.increasing l4)) (PreH16 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH17 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) < (numsSize_pre - i)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ (j = (Zlength (l1))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ ((j + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  (((nums_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) l3 (0 : Int))))
  ** (intArray.missing_i nums_pre (j + 1) (0 : Int) numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_3 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int))) ” &&
  “ ((j + 1) < (numsSize_pre - i)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ (j = (Zlength (l1))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ ((j + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |-> ((Znth j l3 (0 : Int))))
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_4 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int))) ” &&
  “ ((j + 1) < (numsSize_pre - i)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ (j = (Zlength (l1))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ ((j + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  (((nums_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) l3 (0 : Int))))
  ** (intArray.missing_i nums_pre (j + 1) (0 : Int) numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_5 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int))) ” &&
  “ ((j + 1) < (numsSize_pre - i)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ (j = (Zlength (l1))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ ((j + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_6 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (i : Int) (l1 : (List Int)) (key : Int) (l2 : (List Int)) (l4 : (List Int)) (l3 : (List Int)) (PreH1 : ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int)))) (PreH2 : ((j + 1) < (numsSize_pre - i))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = ((l1 ++ (key :: l2)) ++ l4))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : ((0 : Int) <= j)) (PreH13 : ((j + 1) <= (numsSize_pre - i))) (PreH14 : ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2)))))) (PreH15 : (Permutation l l3)) (PreH16 : (Sorting.increasing l4)) (PreH17 : (prefix_suffix_sorted (l1 ++ (key :: l2)) l4)) (PreH18 : (prefix_suffix_sorted l1 (key :: (@List.nil Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1) l3 (0 : Int))) (l3)))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((Znth j l3 (0 : Int)) > (Znth (j + 1) l3 (0 : Int))) ” &&
  “ ((j + 1) < (numsSize_pre - i)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l3 = ((l1 ++ (key :: l2)) ++ l4)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l4))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (i < (numsSize_pre - 1)) ” &&
  “ (j = (Zlength (l1))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ ((j + 1) <= (numsSize_pre - i)) ” &&
  “ ((numsSize_pre - i) = (Zlength ((l1 ++ (key :: l2))))) ” &&
  “ (Permutation l l3) ” &&
  “ (Sorting.increasing l4) ” &&
  “ (prefix_suffix_sorted (l1 ++ (key :: l2)) l4) ” &&
  “ (prefix_suffix_sorted l1 (key :: (@List.nil Int))) ”
  &&  (((nums_pre + ((j + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nums_pre (j + 1) (0 : Int) numsSize_pre (replace_Znth (j) ((Znth (j + 1) l3 (0 : Int))) (l3)))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))


structure VC_Correct : Type where
  proof_of_sortArray_safety_wit_1 : sortArray_safety_wit_1
  proof_of_sortArray_safety_wit_2 : sortArray_safety_wit_2
  proof_of_sortArray_safety_wit_3 : sortArray_safety_wit_3
  proof_of_sortArray_safety_wit_4 : sortArray_safety_wit_4
  proof_of_sortArray_safety_wit_5 : sortArray_safety_wit_5
  proof_of_sortArray_safety_wit_6 : sortArray_safety_wit_6
  proof_of_sortArray_safety_wit_7 : sortArray_safety_wit_7
  proof_of_sortArray_safety_wit_8 : sortArray_safety_wit_8
  proof_of_sortArray_safety_wit_9 : sortArray_safety_wit_9
  proof_of_sortArray_safety_wit_10 : sortArray_safety_wit_10
  proof_of_sortArray_safety_wit_11 : sortArray_safety_wit_11
  proof_of_sortArray_safety_wit_12 : sortArray_safety_wit_12
  proof_of_sortArray_safety_wit_13 : sortArray_safety_wit_13
  proof_of_sortArray_safety_wit_14 : sortArray_safety_wit_14
  proof_of_sortArray_safety_wit_15 : sortArray_safety_wit_15
  proof_of_sortArray_safety_wit_16 : sortArray_safety_wit_16
  proof_of_sortArray_safety_wit_17 : sortArray_safety_wit_17
  proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1
  proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2
  proof_of_sortArray_partial_solve_wit_3 : sortArray_partial_solve_wit_3
  proof_of_sortArray_partial_solve_wit_4 : sortArray_partial_solve_wit_4
  proof_of_sortArray_partial_solve_wit_5 : sortArray_partial_solve_wit_5
  proof_of_sortArray_partial_solve_wit_6 : sortArray_partial_solve_wit_6
  proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1
  proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2
  proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1
  proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2
  proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4
  proof_of_sortArray_return_wit_1 : sortArray_return_wit_1
  proof_of_sortArray_return_wit_2 : sortArray_return_wit_2

end Algorithms.bubble_sort.lean.groundtruth.bubble_sort_goal
