import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib
open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance maximum_subarray_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def max_return_wit_1 : Prop :=
  (
forall (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def max_return_wit_1_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre > b_pre)) ,
  (a_pre = (max_Z (a_pre) (b_pre)))

noncomputable def max_return_wit_2 : Prop :=
  (
forall (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def max_return_wit_2_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre <= b_pre)) ,
  (b_pre = (max_Z (a_pre) (b_pre)))

noncomputable def max_sub_array_safety_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def max_sub_array_safety_wit_2 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ False ”

noncomputable def max_sub_array_safety_wit_3 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "cur" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def max_sub_array_safety_wit_4 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "res" ) )) # Int |->_)
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "cur" ) )) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def max_sub_array_safety_wit_5 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (cur = (Znth (0 : Int) l (0 : Int)))) (PreH5 : (res = (Znth (0 : Int) l (0 : Int)))) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 10000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 10000)) (PreH10 : (MaxSuffixSumPrefix l 1 cur)) (PreH11 : (MaxSubarraySumPrefix l 1 res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cur" ) )) # Int |-> (cur))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def max_sub_array_safety_wit_6 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH11 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH12 : (MaxSuffixSumPrefix l i cur)) (PreH13 : (MaxSubarraySumPrefix l i res)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cur" ) )) # Int |-> (cur))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”

noncomputable def max_sub_array_safety_wit_7 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH11 : (MaxSubarraySumPrefix l (i + 1) res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cur" ) )) # Int |-> (cur))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def max_sub_array_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) = (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) = (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((-10000) <= (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) <= 10000) ” &&
  “ ((-10000) <= (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) <= 10000) ” &&
  “ (MaxSuffixSumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ” &&
  “ (MaxSubarraySumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ (MaxSubarraySumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ” &&
  “ (MaxSuffixSumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def max_sub_array_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (MaxSubarraySumPrefix l 1 (Znth (0 : Int) l (0 : Int)))

noncomputable def max_sub_array_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (MaxSuffixSumPrefix l 1 (Znth (0 : Int) l (0 : Int)))

noncomputable def max_sub_array_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (cur = (Znth (0 : Int) l (0 : Int)))) (PreH5 : (res = (Znth (0 : Int) l (0 : Int)))) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 10000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 10000)) (PreH10 : (MaxSuffixSumPrefix l 1 cur)) (PreH11 : (MaxSubarraySumPrefix l 1 res)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l 1 cur) ” &&
  “ (MaxSubarraySumPrefix l 1 res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (cur = (Znth (0 : Int) l (0 : Int)))) (PreH5 : (res = (Znth (0 : Int) l (0 : Int)))) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 10000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 10000)) (PreH10 : (MaxSuffixSumPrefix l 1 cur)) (PreH11 : (MaxSubarraySumPrefix l 1 res)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (cur = (Znth (0 : Int) l (0 : Int)))) (PreH5 : (res = (Znth (0 : Int) l (0 : Int)))) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 10000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 10000)) (PreH10 : (MaxSuffixSumPrefix l 1 cur)) (PreH11 : (MaxSubarraySumPrefix l 1 res)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def max_sub_array_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (INT_MIN <= (cur + (Znth i l (0 : Int)))) ” &&
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def max_sub_array_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH12 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((-10000) <= retval) ” &&
  “ (retval <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l (i + 1) retval) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH12 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ (MaxSuffixSumPrefix l (i + 1) retval) ” &&
  “ (retval <= 1000000000) ” &&
  “ ((-10000) <= retval) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH12 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def max_sub_array_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH12 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (MaxSuffixSumPrefix l (i + 1) retval)

noncomputable def max_sub_array_entail_wit_4_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH12 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (retval <= 1000000000)

noncomputable def max_sub_array_entail_wit_4_split_goal_4 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH12 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  ((-10000) <= retval)

noncomputable def max_sub_array_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z (res) (cur)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= retval) ” &&
  “ (retval <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l (i + 1) cur) ” &&
  “ (MaxSubarraySumPrefix l (i + 1) retval) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z (res) (cur)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ (MaxSubarraySumPrefix l (i + 1) retval) ” &&
  “ (retval <= 1000000000) ” &&
  “ ((-10000) <= retval) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z (res) (cur)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def max_sub_array_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z (res) (cur)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (MaxSubarraySumPrefix l (i + 1) retval)

noncomputable def max_sub_array_entail_wit_5_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z (res) (cur)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (retval <= 1000000000)

noncomputable def max_sub_array_entail_wit_5_split_goal_4 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (retval : Int) (PreH1 : (retval = (max_Z (res) (cur)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  ((-10000) <= retval)

noncomputable def max_sub_array_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH11 : (MaxSubarraySumPrefix l (i + 1) res)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l (i + 1) cur) ” &&
  “ (MaxSubarraySumPrefix l (i + 1) res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH11 : (MaxSubarraySumPrefix l (i + 1) res)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_6_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH11 : (MaxSubarraySumPrefix l (i + 1) res)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def max_sub_array_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (cur : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l n_pre cur) ” &&
  “ (MaxSubarraySumPrefix l n_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (res : Int) (cur : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ (MaxSubarraySumPrefix l n_pre res) ” &&
  “ (MaxSuffixSumPrefix l n_pre cur) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (res : Int) (cur : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (MaxSubarraySumPrefix l n_pre res)

noncomputable def max_sub_array_entail_wit_7_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (res : Int) (cur : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (MaxSuffixSumPrefix l n_pre cur)

noncomputable def max_sub_array_return_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((-10000) <= cur)) (PreH5 : (cur <= 1000000000)) (PreH6 : (MaxSuffixSumPrefix l n_pre cur)) (PreH7 : (MaxSubarraySumPrefix l n_pre res)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (MaxSubarraySumPrefix l n_pre res) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def max_sub_array_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (n_pre ≠ (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (((arr_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** (intArray.missing_i arr_pre (0 : Int) (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (n_pre ≠ (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (((arr_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** (intArray.missing_i arr_pre (0 : Int) (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH11 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH12 : (MaxSuffixSumPrefix l i cur)) (PreH13 : (MaxSubarraySumPrefix l i res)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (INT_MIN <= (cur + (Znth i l (0 : Int)))) ” &&
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH11 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH12 : (MaxSuffixSumPrefix l i cur)) (PreH13 : (MaxSubarraySumPrefix l i res)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (INT_MIN <= (cur + (Znth i l (0 : Int)))) ” &&
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (INT_MIN <= (cur + (Znth i l (0 : Int))))) (PreH11 : ((cur + (Znth i l (0 : Int))) <= INT_MAX)) (PreH12 : (MaxSuffixSumPrefix l i cur)) (PreH13 : (MaxSubarraySumPrefix l i res)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (INT_MIN <= (cur + (Znth i l (0 : Int)))) ” &&
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def max_sub_array_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (cur : Int) (res : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((-10000) <= cur)) (PreH7 : (cur <= 1000000000)) (PreH8 : ((-10000) <= res)) (PreH9 : (res <= 1000000000)) (PreH10 : (MaxSuffixSumPrefix l (i + 1) cur)) (PreH11 : (MaxSubarraySumPrefix l i res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l (i + 1) cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((-10000) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  (intArray.full arr_pre n_pre l)


structure VC_Correct : Type where
  proof_of_max_sub_array_safety_wit_1 : max_sub_array_safety_wit_1
  proof_of_max_sub_array_safety_wit_2 : max_sub_array_safety_wit_2
  proof_of_max_sub_array_safety_wit_3 : max_sub_array_safety_wit_3
  proof_of_max_sub_array_safety_wit_4 : max_sub_array_safety_wit_4
  proof_of_max_sub_array_safety_wit_5 : max_sub_array_safety_wit_5
  proof_of_max_sub_array_safety_wit_6 : max_sub_array_safety_wit_6
  proof_of_max_sub_array_safety_wit_7 : max_sub_array_safety_wit_7
  proof_of_max_sub_array_return_wit_1 : max_sub_array_return_wit_1
  proof_of_max_sub_array_partial_solve_wit_1 : max_sub_array_partial_solve_wit_1
  proof_of_max_sub_array_partial_solve_wit_2 : max_sub_array_partial_solve_wit_2
  proof_of_max_sub_array_partial_solve_wit_3 : max_sub_array_partial_solve_wit_3
  proof_of_max_sub_array_partial_solve_wit_4 : max_sub_array_partial_solve_wit_4
  proof_of_max_sub_array_partial_solve_wit_5 : max_sub_array_partial_solve_wit_5
  proof_of_max_sub_array_partial_solve_wit_6 : max_sub_array_partial_solve_wit_6
  proof_of_max_return_wit_1 : max_return_wit_1
  proof_of_max_return_wit_2 : max_return_wit_2
  proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1
  proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2
  proof_of_max_sub_array_entail_wit_3 : max_sub_array_entail_wit_3
  proof_of_max_sub_array_entail_wit_4 : max_sub_array_entail_wit_4
  proof_of_max_sub_array_entail_wit_5 : max_sub_array_entail_wit_5
  proof_of_max_sub_array_entail_wit_6 : max_sub_array_entail_wit_6
  proof_of_max_sub_array_entail_wit_7 : max_sub_array_entail_wit_7

end SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal
