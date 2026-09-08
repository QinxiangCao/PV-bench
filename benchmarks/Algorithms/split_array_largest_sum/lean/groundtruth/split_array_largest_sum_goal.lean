import SimpleC.SL.SeparationLogic

import Algorithms.split_array_largest_sum.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance split_array_largest_sum_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def check_safety_wit_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) ,
  ((( &( "cnt" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def check_safety_wit_2 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) ,
  ((( &( "cur" ) )) # Int |->_)
  ** ((( &( "cnt" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_safety_wit_3 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "cur" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "cnt" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_safety_wit_4 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_safety_wit_5 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”

noncomputable def check_safety_wit_6 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((cnt + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cnt + 1)) ”

noncomputable def check_safety_wit_7 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def check_safety_wit_8 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”

noncomputable def check_safety_wit_9 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> ((cnt + 1)))
  ** ((( &( "cur" ) )) # Int |-> ((Znth i l (0 : Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def check_safety_wit_10 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> ((cur + (Znth i l (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def check_safety_wit_11 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def check_safety_wit_12 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_entail_wit_1 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= ((0 : Int) + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (PrefixSplitState l cap_pre (0 : Int) 1 (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) ,
  TT && emp 
|--
  “ (PrefixSplitState l cap_pre (0 : Int) 1 (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000))) ”
  &&  emp
)

noncomputable def check_entail_wit_1_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) ,
  (PrefixSplitState l cap_pre (0 : Int) 1 (0 : Int))

noncomputable def check_entail_wit_1_split_goal_2 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))

noncomputable def check_entail_wit_2_1 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (1 <= (cnt + 1)) ” &&
  “ ((cnt + 1) <= ((i + 1) + 1)) ” &&
  “ ((0 : Int) <= (Znth i l (0 : Int))) ” &&
  “ ((Znth i l (0 : Int)) <= cap_pre) ” &&
  “ (PrefixSplitState l cap_pre (i + 1) (cnt + 1) (Znth i l (0 : Int))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  TT && emp 
|--
  “ (PrefixSplitState l cap_pre (i + 1) (cnt + 1) (Znth i l (0 : Int))) ”
  &&  emp
)

noncomputable def check_entail_wit_2_1_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (PrefixSplitState l cap_pre (i + 1) (cnt + 1) (Znth i l (0 : Int)))

noncomputable def check_entail_wit_2_2 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (1 <= cnt) ” &&
  “ (cnt <= ((i + 1) + 1)) ” &&
  “ ((0 : Int) <= (cur + (Znth i l (0 : Int)))) ” &&
  “ ((cur + (Znth i l (0 : Int))) <= cap_pre) ” &&
  “ (PrefixSplitState l cap_pre (i + 1) cnt (cur + (Znth i l (0 : Int)))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  TT && emp 
|--
  “ (PrefixSplitState l cap_pre (i + 1) cnt (cur + (Znth i l (0 : Int)))) ”
  &&  emp
)

noncomputable def check_entail_wit_2_2_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (PrefixSplitState l cap_pre (i + 1) cnt (cur + (Znth i l (0 : Int))))

noncomputable def check_return_wit_1 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (((0 : Int) = 1) -> (CanSplit l m_pre cap_pre)) ” &&
  “ (((0 : Int) = (0 : Int)) -> (CannotSplit l m_pre cap_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  TT && emp 
|--
  “ (((0 : Int) = (0 : Int)) -> (CannotSplit l m_pre cap_pre)) ”
  &&  emp
)

noncomputable def check_return_wit_1_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (((0 : Int) = (0 : Int)) -> (CannotSplit l m_pre cap_pre))

noncomputable def check_return_wit_2 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= 1) ” &&
  “ ((1 = 1) -> (CanSplit l m_pre cap_pre)) ” &&
  “ ((1 = (0 : Int)) -> (CannotSplit l m_pre cap_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  TT && emp 
|--
  “ ((1 = 1) -> (CanSplit l m_pre cap_pre)) ”
  &&  emp
)

noncomputable def check_return_wit_2_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  ((1 = 1) -> (CanSplit l m_pre cap_pre))

noncomputable def check_return_wit_3 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (((0 : Int) = 1) -> (CanSplit l m_pre cap_pre)) ” &&
  “ (((0 : Int) = (0 : Int)) -> (CannotSplit l m_pre cap_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  TT && emp 
|--
  “ (((0 : Int) = (0 : Int)) -> (CannotSplit l m_pre cap_pre)) ”
  &&  emp
)

noncomputable def check_return_wit_3_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (((0 : Int) = (0 : Int)) -> (CannotSplit l m_pre cap_pre))

noncomputable def check_partial_solve_wit_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((0 : Int) <= cap_pre)) (PreH7 : (cap_pre <= 1000000000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= cnt)) (PreH13 : (cnt <= (i + 1))) (PreH14 : ((0 : Int) <= cur)) (PreH15 : (cur <= cap_pre)) (PreH16 : (PrefixSplitState l cap_pre i cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= cnt) ” &&
  “ (cnt <= (i + 1)) ” &&
  “ ((0 : Int) <= cur) ” &&
  “ (cur <= cap_pre) ” &&
  “ (PrefixSplitState l cap_pre i cnt cur) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)

noncomputable def splitArrayLargestSum_safety_wit_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans <= 1000000000)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def splitArrayLargestSum_safety_wit_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans <= 1000000000)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1000000000 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000000) ”

noncomputable def splitArrayLargestSum_safety_wit_3 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + (Z.quot (right - left) 2))) ”
) \/
(
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + (Z.quot (right - left) 2))) ”
)

noncomputable def splitArrayLargestSum_safety_wit_3_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= INT_MAX) ”

noncomputable def splitArrayLargestSum_safety_wit_3_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((INT_MIN) <= (left + (Z.quot (right - left) 2))) ”

noncomputable def splitArrayLargestSum_safety_wit_4 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((right - left) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def splitArrayLargestSum_safety_wit_5 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((right - left) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right - left)) ”

noncomputable def splitArrayLargestSum_safety_wit_6 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def splitArrayLargestSum_safety_wit_7 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res)) (PreH18 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((left + (Z.quot (right - left) 2)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + (Z.quot (right - left) 2)) + 1)) ”
) \/
(
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res)) (PreH18 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((left + (Z.quot (right - left) 2)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + (Z.quot (right - left) 2)) + 1)) ”
)

noncomputable def splitArrayLargestSum_safety_wit_7_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res)) (PreH18 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((left + (Z.quot (right - left) 2)) + 1) <= INT_MAX) ”

noncomputable def splitArrayLargestSum_safety_wit_7_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res)) (PreH18 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((INT_MIN) <= ((left + (Z.quot (right - left) 2)) + 1)) ”

noncomputable def splitArrayLargestSum_safety_wit_8 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res)) (PreH18 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def splitArrayLargestSum_entail_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans <= 1000000000)) ,
  (intArray.full arr_pre n_pre l)
|--
  EX res : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (1000000000 <= 1000000000) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans <= 1000000000)) ,
  TT && emp 
|--
  EX res : Int,
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (1000000000 <= 1000000000) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_entail_wit_2_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH18 : (retval ≠ (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX res : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ (left <= (left + (Z.quot (right - left) 2))) ” &&
  “ (left <= res) ” &&
  “ (res <= (left + (Z.quot (right - left) 2))) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH18 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  EX res : Int,
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ (left <= (left + (Z.quot (right - left) 2))) ” &&
  “ (left <= res) ” &&
  “ (res <= (left + (Z.quot (right - left) 2))) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_entail_wit_2_2 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH18 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX res : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= ((left + (Z.quot (right - left) 2)) + 1)) ” &&
  “ (right <= 1000000000) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= right) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= res) ” &&
  “ (res <= right) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (CannotSplit l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH18 : (retval = (0 : Int))) ,
  TT && emp 
|--
  EX res : Int,
  “ ((0 : Int) <= ((left + (Z.quot (right - left) 2)) + 1)) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= right) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= res) ” &&
  “ (res <= right) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_return_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (MinimizedMaxSegmentSum l m_pre left) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  TT && emp 
|--
  “ (MinimizedMaxSegmentSum l m_pre left) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_return_wit_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  (MinimizedMaxSegmentSum l m_pre left)

noncomputable def splitArrayLargestSum_partial_solve_wit_1_pure : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000))) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ”
) \/
(
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + (Z.quot (right - left) 2)) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + (Z.quot (right - left) 2)) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH18 : ((0 : Int) <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000))) ”
)

noncomputable def splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + (Z.quot (right - left) 2)) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + (Z.quot (right - left) 2)) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH18 : ((0 : Int) <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ”

noncomputable def splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + (Z.quot (right - left) 2)) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + (Z.quot (right - left) 2)) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH18 : ((0 : Int) <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ”

noncomputable def splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_3 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + (Z.quot (right - left) 2)) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + (Z.quot (right - left) 2)) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH18 : ((0 : Int) <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000))) ”

noncomputable def splitArrayLargestSum_partial_solve_wit_1_aux : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000)))) (PreH8 : ((0 : Int) <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100000000))) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ” &&
  “ (left < right) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100000000))) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (right <= 1000000000) ” &&
  “ (left <= right) ” &&
  “ (left <= res) ” &&
  “ (res <= right) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def splitArrayLargestSum_partial_solve_wit_1 : Prop := splitArrayLargestSum_partial_solve_wit_1_pure -> splitArrayLargestSum_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_check_safety_wit_1 : check_safety_wit_1
  proof_of_check_safety_wit_2 : check_safety_wit_2
  proof_of_check_safety_wit_3 : check_safety_wit_3
  proof_of_check_safety_wit_4 : check_safety_wit_4
  proof_of_check_safety_wit_5 : check_safety_wit_5
  proof_of_check_safety_wit_6 : check_safety_wit_6
  proof_of_check_safety_wit_7 : check_safety_wit_7
  proof_of_check_safety_wit_8 : check_safety_wit_8
  proof_of_check_safety_wit_9 : check_safety_wit_9
  proof_of_check_safety_wit_10 : check_safety_wit_10
  proof_of_check_safety_wit_11 : check_safety_wit_11
  proof_of_check_safety_wit_12 : check_safety_wit_12
  proof_of_check_partial_solve_wit_1 : check_partial_solve_wit_1
  proof_of_splitArrayLargestSum_safety_wit_1 : splitArrayLargestSum_safety_wit_1
  proof_of_splitArrayLargestSum_safety_wit_2 : splitArrayLargestSum_safety_wit_2
  proof_of_splitArrayLargestSum_safety_wit_4 : splitArrayLargestSum_safety_wit_4
  proof_of_splitArrayLargestSum_safety_wit_5 : splitArrayLargestSum_safety_wit_5
  proof_of_splitArrayLargestSum_safety_wit_6 : splitArrayLargestSum_safety_wit_6
  proof_of_splitArrayLargestSum_safety_wit_8 : splitArrayLargestSum_safety_wit_8
  proof_of_splitArrayLargestSum_partial_solve_wit_1 : splitArrayLargestSum_partial_solve_wit_1
  proof_of_check_entail_wit_1 : check_entail_wit_1
  proof_of_check_entail_wit_2_1 : check_entail_wit_2_1
  proof_of_check_entail_wit_2_2 : check_entail_wit_2_2
  proof_of_check_return_wit_1 : check_return_wit_1
  proof_of_check_return_wit_2 : check_return_wit_2
  proof_of_check_return_wit_3 : check_return_wit_3
  proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3
  proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7
  proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1
  proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1
  proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2
  proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1
  proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure

end Algorithms.split_array_largest_sum.lean.groundtruth.split_array_largest_sum_goal
