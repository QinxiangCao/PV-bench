import SimpleC.SL.SeparationLogic

import Algorithms.choosing_inns.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.choosing_inns.lean.groundtruth.choosing_inns_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance choosing_inns_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def initCounts_safety_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def initCounts_safety_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i)) (PreH7 : (CountsZeroPrefix good_l i)) ,
  ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg seen_pre (0 : Int) i seen_l)
  ** (intArray.undef_seg seen_pre i k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def initCounts_safety_wit_3 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i)) (PreH7 : (CountsZeroPrefix good_l i)) ,
  (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def initCounts_safety_wit_4 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (seen_l : (List Int)) (good_l : (List Int)) (i : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountsZeroPrefix seen_l (i + 1))) (PreH6 : (CountsZeroPrefix good_l (i + 1))) ,
  ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg seen_pre (0 : Int) (i + 1) seen_l)
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) (i + 1) good_l)
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def initCounts_entail_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= k_pre) ” &&
  “ (CountsZeroPrefix seen_l (0 : Int)) ” &&
  “ (CountsZeroPrefix good_l (0 : Int)) ”
  &&  (intArray.seg seen_pre (0 : Int) (0 : Int) seen_l)
  ** (intArray.undef_seg seen_pre (0 : Int) k_pre)
  ** (intArray.seg good_pre (0 : Int) (0 : Int) good_l)
  ** (intArray.undef_seg good_pre (0 : Int) k_pre)
) \/
(
forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (@List.nil Int) (0 : Int)) ” &&
  “ (CountsZeroPrefix (@List.nil Int) (0 : Int)) ”
  &&  emp
)

noncomputable def initCounts_entail_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (CountsZeroPrefix (@List.nil Int) (0 : Int))

noncomputable def initCounts_entail_wit_1_split_goal_2 : Prop :=
  forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (CountsZeroPrefix (@List.nil Int) (0 : Int))

noncomputable def initCounts_entail_wit_2 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i)) (PreH7 : (CountsZeroPrefix good_l_2 i)) ,
  (intArray.seg good_pre (0 : Int) (i + 1) (good_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
  ** (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < k_pre) ” &&
  “ (CountsZeroPrefix seen_l (i + 1)) ” &&
  “ (CountsZeroPrefix good_l (i + 1)) ”
  &&  (intArray.seg seen_pre (0 : Int) (i + 1) seen_l)
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) (i + 1) good_l)
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
) \/
(
forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i)) (PreH7 : (CountsZeroPrefix good_l_2 i)) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (good_l_2 ++ ((0 : Int) :: (@List.nil Int))) (i + 1)) ” &&
  “ (CountsZeroPrefix (seen_l_2 ++ ((0 : Int) :: (@List.nil Int))) (i + 1)) ”
  &&  emp
)

noncomputable def initCounts_entail_wit_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i)) (PreH7 : (CountsZeroPrefix good_l_2 i)) ,
  (CountsZeroPrefix (good_l_2 ++ ((0 : Int) :: (@List.nil Int))) (i + 1))

noncomputable def initCounts_entail_wit_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i)) (PreH7 : (CountsZeroPrefix good_l_2 i)) ,
  (CountsZeroPrefix (seen_l_2 ++ ((0 : Int) :: (@List.nil Int))) (i + 1))

noncomputable def initCounts_entail_wit_3 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (i : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountsZeroPrefix seen_l_2 (i + 1))) (PreH6 : (CountsZeroPrefix good_l_2 (i + 1))) ,
  (intArray.seg seen_pre (0 : Int) (i + 1) seen_l_2)
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) (i + 1) good_l_2)
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= k_pre) ” &&
  “ (CountsZeroPrefix seen_l (i + 1)) ” &&
  “ (CountsZeroPrefix good_l (i + 1)) ”
  &&  (intArray.seg seen_pre (0 : Int) (i + 1) seen_l)
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) (i + 1) good_l)
  ** (intArray.undef_seg good_pre (i + 1) k_pre)

noncomputable def initCounts_return_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i)) (PreH7 : (CountsZeroPrefix good_l_2 i)) ,
  (intArray.seg seen_pre (0 : Int) i seen_l_2)
  ** (intArray.undef_seg seen_pre i k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l_2)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (CountsZeroFull k_pre seen_l) ” &&
  “ (CountsZeroFull k_pre good_l) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
) \/
(
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i)) (PreH7 : (CountsZeroPrefix good_l_2 i)) ,
  (intArray.seg seen_pre (0 : Int) i seen_l_2)
  ** (intArray.seg good_pre (0 : Int) i good_l_2)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (CountsZeroFull k_pre seen_l) ” &&
  “ (CountsZeroFull k_pre good_l) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
)

noncomputable def initCounts_partial_solve_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i)) (PreH7 : (CountsZeroPrefix good_l i)) ,
  (intArray.seg seen_pre (0 : Int) i seen_l)
  ** (intArray.undef_seg seen_pre i k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ (CountsZeroPrefix seen_l i) ” &&
  “ (CountsZeroPrefix good_l i) ”
  &&  (((seen_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg seen_pre (0 : Int) i seen_l)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)

noncomputable def initCounts_partial_solve_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i)) (PreH7 : (CountsZeroPrefix good_l i)) ,
  (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ (CountsZeroPrefix seen_l i) ” &&
  “ (CountsZeroPrefix good_l i) ”
  &&  (((good_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
  ** (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)

noncomputable def copyCounts_safety_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000)) (PreH4 : (CountArraySafe good_old k_pre 200000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_old)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def copyCounts_safety_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountArraySafe seen_l k_pre 200000)) (PreH6 : (CountArraySafe good_old k_pre 200000)) (PreH7 : (CountArraySafe good_cur k_pre 200000)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur (i + 1) k_pre)) ,
  ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def copyCounts_entail_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000)) (PreH4 : (CountArraySafe good_old k_pre 200000)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_old)
|--
  EX good_cur : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= k_pre) ” &&
  “ (CountArraySafe seen_l k_pre 200000) ” &&
  “ (CountArraySafe good_old k_pre 200000) ” &&
  “ (CountArraySafe good_cur k_pre 200000) ” &&
  “ (CopyCountsPrefix seen_l good_old good_cur (0 : Int) k_pre) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
) \/
(
forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000)) (PreH4 : (CountArraySafe good_old k_pre 200000)) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old good_old (0 : Int) k_pre) ”
  &&  emp
)

noncomputable def copyCounts_entail_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000)) (PreH4 : (CountArraySafe good_old k_pre 200000)) ,
  (CopyCountsPrefix seen_l good_old good_old (0 : Int) k_pre)

noncomputable def copyCounts_entail_wit_2 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (intArray.full good_pre k_pre (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)))
  ** (intArray.full seen_pre k_pre seen_l)
|--
  EX good_cur : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < k_pre) ” &&
  “ (CountArraySafe seen_l k_pre 200000) ” &&
  “ (CountArraySafe good_old k_pre 200000) ” &&
  “ (CountArraySafe good_cur k_pre 200000) ” &&
  “ (CopyCountsPrefix seen_l good_old good_cur (i + 1) k_pre) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
) \/
(
forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre)) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) (i + 1) k_pre) ” &&
  “ (CountArraySafe (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) k_pre 200000) ”
  &&  emp
)

noncomputable def copyCounts_entail_wit_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) (i + 1) k_pre)

noncomputable def copyCounts_entail_wit_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (CountArraySafe (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) k_pre 200000)

noncomputable def copyCounts_entail_wit_3 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountArraySafe seen_l k_pre 200000)) (PreH6 : (CountArraySafe good_old k_pre 200000)) (PreH7 : (CountArraySafe good_cur_2 k_pre 200000)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur_2 (i + 1) k_pre)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur_2)
|--
  EX good_cur : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= k_pre) ” &&
  “ (CountArraySafe seen_l k_pre 200000) ” &&
  “ (CountArraySafe good_old k_pre 200000) ” &&
  “ (CountArraySafe good_cur k_pre 200000) ” &&
  “ (CopyCountsPrefix seen_l good_old good_cur (i + 1) k_pre) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)

noncomputable def copyCounts_return_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
|--
  “ (CountArraySafe seen_l k_pre 200000) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre seen_l)
) \/
(
forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre)) ,
  TT && emp 
|--
  “ (good_cur = seen_l) ”
  &&  emp
)

noncomputable def copyCounts_return_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre)) ,
  (good_cur = seen_l)

noncomputable def copyCounts_partial_solve_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ (CountArraySafe seen_l k_pre 200000) ” &&
  “ (CountArraySafe good_old k_pre 200000) ” &&
  “ (CountArraySafe good_cur k_pre 200000) ” &&
  “ (CopyCountsPrefix seen_l good_old good_cur i k_pre) ”
  &&  (((seen_pre + (i * sizeof(INT)))) # Int |-> ((Znth i seen_l (0 : Int))))
  ** (intArray.missing_i seen_pre i (0 : Int) k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)

noncomputable def copyCounts_partial_solve_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000)) (PreH7 : (CountArraySafe good_old k_pre 200000)) (PreH8 : (CountArraySafe good_cur k_pre 200000)) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ (CountArraySafe seen_l k_pre 200000) ” &&
  “ (CountArraySafe good_old k_pre 200000) ” &&
  “ (CountArraySafe good_cur k_pre 200000) ” &&
  “ (CopyCountsPrefix seen_l good_old good_cur i k_pre) ”
  &&  (((good_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i good_pre i (0 : Int) k_pre good_cur)
  ** (intArray.full seen_pre k_pre seen_l)

noncomputable def countChoosingInns_safety_wit_1 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  ((( &( "answer" ) )) # Int64 |->_)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_2 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : (CountsZeroFull k_pre seen_l)) (PreH4 : (CountsZeroFull k_pre good_l)) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l good_l)) (PreH6 : (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre (0 : Int) seen_l good_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_3 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (answer + (Znth c seen_l (0 : Int)))) ”

noncomputable def countChoosingInns_safety_wit_4 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c seen_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth c seen_l (0 : Int)) + 1)) ”

noncomputable def countChoosingInns_safety_wit_5 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c seen_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def countChoosingInns_safety_wit_6 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full good_pre k_pre good_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
|--
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (answer + (Znth c good_l (0 : Int)))) ”

noncomputable def countChoosingInns_safety_wit_7 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c good_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth c seen_l (0 : Int)) + 1)) ”

noncomputable def countChoosingInns_safety_wit_8 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c good_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def countChoosingInns_safety_wit_9 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c < k_pre)) (PreH8 : ((0 : Int) <= answer)) (PreH9 : (answer <= 19999900000)) (PreH10 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next seen_next)) (PreH11 : (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next seen_next)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre seen_next)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def countChoosingInns_safety_wit_10 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH4 : (p_pre < cost)) (PreH5 : (cost <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= c)) (PreH9 : (c < k_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l)) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c good_l (0 : Int))) seen_l good_l)) (PreH16 : (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next good_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def countChoosingInns_entail_wit_1 : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (PreH1 : (CountsZeroFull k_pre seen_l_2)) (PreH2 : (CountsZeroFull k_pre good_l_2)) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  (intArray.full seen_pre k_pre seen_l_2)
  ** (intArray.full good_pre k_pre good_l_2)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ (CountsZeroFull k_pre seen_l) ” &&
  “ (CountsZeroFull k_pre good_l) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre (0 : Int) seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (PreH1 : (CountsZeroFull k_pre seen_l_2)) (PreH2 : (CountsZeroFull k_pre good_l_2)) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  TT && emp 
|--
  “ (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre (0 : Int) seen_l_2 good_l_2) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l_2 good_l_2) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_1_split_goal_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (PreH1 : (CountsZeroFull k_pre seen_l_2)) (PreH2 : (CountsZeroFull k_pre good_l_2)) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre (0 : Int) seen_l_2 good_l_2)

noncomputable def countChoosingInns_entail_wit_1_split_goal_2 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (PreH1 : (CountsZeroFull k_pre seen_l_2)) (PreH2 : (CountsZeroFull k_pre good_l_2)) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l_2 good_l_2)

noncomputable def countChoosingInns_entail_wit_2 : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : (CountsZeroFull k_pre seen_l_2)) (PreH4 : (CountsZeroFull k_pre good_l_2)) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l_2 good_l_2)) (PreH6 : (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre (0 : Int) seen_l_2 good_l_2)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l_2)
  ** (intArray.full good_pre k_pre good_l_2)
|--
  EX seen_l : (List Int), EX good_l : (List Int),
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : (CountsZeroFull k_pre seen_l_2)) (PreH4 : (CountsZeroFull k_pre good_l_2)) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l_2 good_l_2)) (PreH6 : (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre (0 : Int) seen_l_2 good_l_2)) ,
  TT && emp 
|--
  “ ((0 : Int) <= n_pre) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_2_split_goal_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : (CountsZeroFull k_pre seen_l_2)) (PreH4 : (CountsZeroFull k_pre good_l_2)) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l (0 : Int) k_pre seen_l_2 good_l_2)) (PreH6 : (ChoosingPrefixState colors_l costs_l (0 : Int) k_pre p_pre (0 : Int) seen_l_2 good_l_2)) ,
  ((0 : Int) <= n_pre)

noncomputable def countChoosingInns_entail_wit_3 : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full seen_pre k_pre seen_l_2)
  ** (intArray.full good_pre k_pre good_l_2)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((Znth i colors_l (0 : Int)) = (Znth i colors_l (0 : Int))) ” &&
  “ ((Znth i costs_l (0 : Int)) = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (Znth i colors_l (0 : Int))) ” &&
  “ ((Znth i colors_l (0 : Int)) < k_pre) ” &&
  “ ((0 : Int) <= (Znth i costs_l (0 : Int))) ” &&
  “ ((Znth i costs_l (0 : Int)) <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int))) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  TT && emp 
|--
  “ (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int))) <= 9223372036854775807) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int))) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int))) ” &&
  “ ((Znth i costs_l (0 : Int)) <= 100) ” &&
  “ ((0 : Int) <= (Znth i costs_l (0 : Int))) ” &&
  “ ((Znth i colors_l (0 : Int)) < k_pre) ” &&
  “ ((0 : Int) <= (Znth i colors_l (0 : Int))) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_3_split_goal_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1) <= INT_MAX)

noncomputable def countChoosingInns_entail_wit_3_split_goal_2 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((answer + (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int))) <= 9223372036854775807)

noncomputable def countChoosingInns_entail_wit_3_split_goal_3 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int))) <= 9223372036854775807)

noncomputable def countChoosingInns_entail_wit_3_split_goal_4 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int)) <= i)

noncomputable def countChoosingInns_entail_wit_3_split_goal_5 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int)))

noncomputable def countChoosingInns_entail_wit_3_split_goal_6 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) <= i)

noncomputable def countChoosingInns_entail_wit_3_split_goal_7 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)))

noncomputable def countChoosingInns_entail_wit_3_split_goal_8 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth i costs_l (0 : Int)) <= 100)

noncomputable def countChoosingInns_entail_wit_3_split_goal_9 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth i costs_l (0 : Int)))

noncomputable def countChoosingInns_entail_wit_3_split_goal_10 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth i colors_l (0 : Int)) < k_pre)

noncomputable def countChoosingInns_entail_wit_3_split_goal_11 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth i colors_l (0 : Int)))

noncomputable def countChoosingInns_entail_wit_4 : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l_2 : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l_2 (0 : Int)))) (PreH16 : ((Znth c good_l_2 (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l_2 (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2)) ,
  (intArray.full seen_pre k_pre (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l_2)
|--
  EX good_l : (List Int), EX seen_l_2 : (List Int), EX seen_next : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= (answer + (Znth c seen_l (0 : Int)))) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 19999900000) ” &&
  “ (seen_next = (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2))) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l (0 : Int))) - (Znth c seen_l_2 (0 : Int))) seen_l_2 good_l) ” &&
  “ (CountArraySafe seen_next k_pre 200000) ” &&
  “ (CountArraySafe good_l k_pre 200000) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l_2 : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l_2 (0 : Int)))) (PreH16 : ((Znth c good_l_2 (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l_2 (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2)) ,
  TT && emp 
|--
  EX seen_l_2 : (List Int),
  “ ((replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l)) = (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1)) (seen_l_2))) ” &&
  “ ((0 : Int) <= (answer + (Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)))) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int))) <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1)) (seen_l_2)) good_l_2) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int))) - (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int))) seen_l_2 good_l_2) ” &&
  “ (CountArraySafe (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1)) (seen_l_2)) k_pre 200000) ” &&
  “ (CountArraySafe good_l_2 k_pre 200000) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_5 : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c < k_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 good_l)) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH18 : (CountArraySafe good_l k_pre 200000)) ,
  (intArray.full seen_pre k_pre seen_next_2)
  ** (intArray.full good_pre k_pre seen_next_2)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  EX seen_next : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next seen_next) ” &&
  “ (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next seen_next) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre seen_next)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c < k_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 good_l)) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH18 : (CountArraySafe good_l k_pre 200000)) ,
  TT && emp 
|--
  “ (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next_2 seen_next_2) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 seen_next_2) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_5_split_goal_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c < k_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 good_l)) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH18 : (CountArraySafe good_l k_pre 200000)) ,
  (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next_2 seen_next_2)

noncomputable def countChoosingInns_entail_wit_5_split_goal_2 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c < k_pre)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 good_l)) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000)) (PreH18 : (CountArraySafe good_l k_pre 200000)) ,
  (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next_2 seen_next_2)

noncomputable def countChoosingInns_entail_wit_6 : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l_2 (0 : Int)))) (PreH14 : ((Znth c seen_l_2 (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l_2 (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l_2 (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l)) ,
  (intArray.full seen_pre k_pre (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2)))
  ** (intArray.full good_pre k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  EX good_l_2 : (List Int), EX seen_l : (List Int), EX seen_next : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ (p_pre < cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= (answer + (Znth c good_l (0 : Int)))) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 19999900000) ” &&
  “ (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l_2) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c good_l (0 : Int))) - (Znth c good_l_2 (0 : Int))) seen_l good_l_2) ” &&
  “ (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre (answer + (Znth c good_l (0 : Int))) seen_next good_l_2) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l_2)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l_2 (0 : Int)))) (PreH14 : ((Znth c seen_l_2 (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l_2 (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l_2 (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l)) ,
  TT && emp 
|--
  EX seen_l : (List Int),
  “ ((replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1)) (seen_l_2)) = (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ (p_pre < (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= (answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int)))) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l)) good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) - (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre (answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l)) good_l) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_7_1 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c < k_pre)) (PreH8 : ((0 : Int) <= answer)) (PreH9 : (answer <= 19999900000)) (PreH10 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next seen_next)) (PreH11 : (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next seen_next)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre seen_next)
|--
  EX seen_l : (List Int), EX good_l : (List Int),
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_entail_wit_7_2 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH4 : (p_pre < cost)) (PreH5 : (cost <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= c)) (PreH9 : (c < k_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l_2)) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c good_l_2 (0 : Int))) seen_l_2 good_l_2)) (PreH16 : (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_next good_l_2)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l_2)
|--
  EX seen_l : (List Int), EX good_l : (List Int),
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_entail_wit_8 : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l_2)
  ** (intArray.full good_pre k_pre good_l_2)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  TT && emp 
|--
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_8_split_goal_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer)

noncomputable def countChoosingInns_return_wit_1 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (answer : Int) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH2 : ((0 : Int) <= answer)) (PreH3 : (answer <= 19999900000)) (PreH4 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l_2)
  ** (intArray.full good_pre k_pre good_l_2)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_partial_solve_wit_1_pure : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  ((( &( "answer" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ (k_pre <= 50) ” &&
  “ (1 <= k_pre) ”
) \/
(
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : ((0 : Int) <= 9223372036854775807)) (PreH2 : ((0 : Int) >= (-9223372036854775808))) (PreH3 : (p_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (p_pre >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  ((( &( "answer" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ”
)

noncomputable def countChoosingInns_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : ((0 : Int) <= 9223372036854775807)) (PreH2 : ((0 : Int) >= (-9223372036854775808))) (PreH3 : (p_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (p_pre >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  ((( &( "answer" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ (1 <= k_pre) ”

noncomputable def countChoosingInns_partial_solve_wit_1_pure_split_goal_2 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : ((0 : Int) <= 9223372036854775807)) (PreH2 : ((0 : Int) >= (-9223372036854775808))) (PreH3 : (p_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (p_pre >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  ((( &( "answer" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ (k_pre <= 50) ”

noncomputable def countChoosingInns_partial_solve_wit_1_aux : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ (k_pre <= 50) ” &&
  “ (1 <= k_pre) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ”
  &&  (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)

noncomputable def countChoosingInns_partial_solve_wit_1 : Prop := countChoosingInns_partial_solve_wit_1_pure -> countChoosingInns_partial_solve_wit_1_aux

noncomputable def countChoosingInns_partial_solve_wit_2 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (i < n_pre) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int |-> ((Znth i colors_l (0 : Int))))
  ** (intArray.missing_i colors_pre i (0 : Int) n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_partial_solve_wit_3 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (i < n_pre) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((costs_pre + (i * sizeof(INT)))) # Int |-> ((Znth i costs_l (0 : Int))))
  ** (intArray.missing_i costs_pre i (0 : Int) n_pre costs_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_partial_solve_wit_4 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (cost <= p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int |-> ((Znth c seen_l (0 : Int))))
  ** (intArray.missing_i seen_pre c (0 : Int) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_partial_solve_wit_5 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (cost <= p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int |-> ((Znth c seen_l (0 : Int))))
  ** (intArray.missing_i seen_pre c (0 : Int) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_partial_solve_wit_6 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (cost <= p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i seen_pre c (0 : Int) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full good_pre k_pre good_l)

noncomputable def countChoosingInns_partial_solve_wit_7_pure : Prop :=
  (
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH4 : ((0 : Int) <= cost)) (PreH5 : (cost <= p_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= c)) (PreH9 : (c < k_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l)) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH16 : (CountArraySafe seen_next k_pre 200000)) (PreH17 : (CountArraySafe good_l k_pre 200000)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (1 <= k_pre) ” &&
  “ (CountArraySafe seen_next k_pre 200000) ” &&
  “ (CountArraySafe good_l k_pre 200000) ” &&
  “ (k_pre <= 50) ”
) \/
(
forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (answer <= 9223372036854775807)) (PreH2 : (answer >= (-9223372036854775808))) (PreH3 : (cost <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (c <= INT_MAX)) (PreH6 : (p_pre <= INT_MAX)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (cost >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (c >= INT_MIN)) (PreH12 : (p_pre >= INT_MIN)) (PreH13 : (k_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (c = (Znth i colors_l (0 : Int)))) (PreH16 : (cost = (Znth i costs_l (0 : Int)))) (PreH17 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH18 : ((0 : Int) <= cost)) (PreH19 : (cost <= p_pre)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < n_pre)) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c < k_pre)) (PreH24 : ((0 : Int) <= answer)) (PreH25 : (answer <= 19999900000)) (PreH26 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH27 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH28 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l)) (PreH29 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH30 : (CountArraySafe seen_next k_pre 200000)) (PreH31 : (CountArraySafe good_l k_pre 200000)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (k_pre <= 50) ”
)

noncomputable def countChoosingInns_partial_solve_wit_7_pure_split_goal_1 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (answer <= 9223372036854775807)) (PreH2 : (answer >= (-9223372036854775808))) (PreH3 : (cost <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (c <= INT_MAX)) (PreH6 : (p_pre <= INT_MAX)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (cost >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (c >= INT_MIN)) (PreH12 : (p_pre >= INT_MIN)) (PreH13 : (k_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (c = (Znth i colors_l (0 : Int)))) (PreH16 : (cost = (Znth i costs_l (0 : Int)))) (PreH17 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH18 : ((0 : Int) <= cost)) (PreH19 : (cost <= p_pre)) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < n_pre)) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c < k_pre)) (PreH24 : ((0 : Int) <= answer)) (PreH25 : (answer <= 19999900000)) (PreH26 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH27 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH28 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l)) (PreH29 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH30 : (CountArraySafe seen_next k_pre 200000)) (PreH31 : (CountArraySafe good_l k_pre 200000)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (k_pre <= 50) ”

noncomputable def countChoosingInns_partial_solve_wit_7_aux : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH4 : ((0 : Int) <= cost)) (PreH5 : (cost <= p_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= c)) (PreH9 : (c < k_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l)) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH16 : (CountArraySafe seen_next k_pre 200000)) (PreH17 : (CountArraySafe good_l k_pre 200000)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (1 <= k_pre) ” &&
  “ (CountArraySafe seen_next k_pre 200000) ” &&
  “ (CountArraySafe good_l k_pre 200000) ” &&
  “ (k_pre <= 50) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre seen_next good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l) ” &&
  “ (CountArraySafe seen_next k_pre 200000) ” &&
  “ (CountArraySafe good_l k_pre 200000) ”
  &&  (intArray.full seen_pre k_pre seen_next)
  ** (intArray.full good_pre k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)

noncomputable def countChoosingInns_partial_solve_wit_7 : Prop := countChoosingInns_partial_solve_wit_7_pure -> countChoosingInns_partial_solve_wit_7_aux

noncomputable def countChoosingInns_partial_solve_wit_8 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
|--
  “ (cost > p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((good_pre + (c * sizeof(INT)))) # Int |-> ((Znth c good_l (0 : Int))))
  ** (intArray.missing_i good_pre c (0 : Int) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)

noncomputable def countChoosingInns_partial_solve_wit_9 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full good_pre k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full seen_pre k_pre seen_l)
|--
  “ (cost > p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int |-> ((Znth c seen_l (0 : Int))))
  ** (intArray.missing_i seen_pre c (0 : Int) k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)

noncomputable def countChoosingInns_partial_solve_wit_10 : Prop :=
  forall (good_pre : Int) (seen_pre : Int) (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c < k_pre)) (PreH9 : ((0 : Int) <= cost)) (PreH10 : (cost <= 100)) (PreH11 : ((0 : Int) <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH14 : ((Znth c seen_l (0 : Int)) <= i)) (PreH15 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH16 : ((Znth c good_l (0 : Int)) <= i)) (PreH17 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH18 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH19 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l)) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  “ (cost > p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l) ” &&
  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i seen_pre c (0 : Int) k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)


structure VC_Correct : Type where
  proof_of_initCounts_safety_wit_1 : initCounts_safety_wit_1
  proof_of_initCounts_safety_wit_2 : initCounts_safety_wit_2
  proof_of_initCounts_safety_wit_3 : initCounts_safety_wit_3
  proof_of_initCounts_safety_wit_4 : initCounts_safety_wit_4
  proof_of_initCounts_entail_wit_3 : initCounts_entail_wit_3
  proof_of_initCounts_partial_solve_wit_1 : initCounts_partial_solve_wit_1
  proof_of_initCounts_partial_solve_wit_2 : initCounts_partial_solve_wit_2
  proof_of_copyCounts_safety_wit_1 : copyCounts_safety_wit_1
  proof_of_copyCounts_safety_wit_2 : copyCounts_safety_wit_2
  proof_of_copyCounts_entail_wit_3 : copyCounts_entail_wit_3
  proof_of_copyCounts_partial_solve_wit_1 : copyCounts_partial_solve_wit_1
  proof_of_copyCounts_partial_solve_wit_2 : copyCounts_partial_solve_wit_2
  proof_of_countChoosingInns_safety_wit_1 : countChoosingInns_safety_wit_1
  proof_of_countChoosingInns_safety_wit_2 : countChoosingInns_safety_wit_2
  proof_of_countChoosingInns_safety_wit_3 : countChoosingInns_safety_wit_3
  proof_of_countChoosingInns_safety_wit_4 : countChoosingInns_safety_wit_4
  proof_of_countChoosingInns_safety_wit_5 : countChoosingInns_safety_wit_5
  proof_of_countChoosingInns_safety_wit_6 : countChoosingInns_safety_wit_6
  proof_of_countChoosingInns_safety_wit_7 : countChoosingInns_safety_wit_7
  proof_of_countChoosingInns_safety_wit_8 : countChoosingInns_safety_wit_8
  proof_of_countChoosingInns_safety_wit_9 : countChoosingInns_safety_wit_9
  proof_of_countChoosingInns_safety_wit_10 : countChoosingInns_safety_wit_10
  proof_of_countChoosingInns_entail_wit_7_1 : countChoosingInns_entail_wit_7_1
  proof_of_countChoosingInns_entail_wit_7_2 : countChoosingInns_entail_wit_7_2
  proof_of_countChoosingInns_return_wit_1 : countChoosingInns_return_wit_1
  proof_of_countChoosingInns_partial_solve_wit_1 : countChoosingInns_partial_solve_wit_1
  proof_of_countChoosingInns_partial_solve_wit_2 : countChoosingInns_partial_solve_wit_2
  proof_of_countChoosingInns_partial_solve_wit_3 : countChoosingInns_partial_solve_wit_3
  proof_of_countChoosingInns_partial_solve_wit_4 : countChoosingInns_partial_solve_wit_4
  proof_of_countChoosingInns_partial_solve_wit_5 : countChoosingInns_partial_solve_wit_5
  proof_of_countChoosingInns_partial_solve_wit_6 : countChoosingInns_partial_solve_wit_6
  proof_of_countChoosingInns_partial_solve_wit_7 : countChoosingInns_partial_solve_wit_7
  proof_of_countChoosingInns_partial_solve_wit_8 : countChoosingInns_partial_solve_wit_8
  proof_of_countChoosingInns_partial_solve_wit_9 : countChoosingInns_partial_solve_wit_9
  proof_of_countChoosingInns_partial_solve_wit_10 : countChoosingInns_partial_solve_wit_10
  proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1
  proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2
  proof_of_initCounts_return_wit_1 : initCounts_return_wit_1
  proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1
  proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2
  proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1
  proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1
  proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2
  proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3
  proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4
  proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5
  proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6
  proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8
  proof_of_countChoosingInns_partial_solve_wit_1_pure : countChoosingInns_partial_solve_wit_1_pure
  proof_of_countChoosingInns_partial_solve_wit_7_pure : countChoosingInns_partial_solve_wit_7_pure

end Algorithms.choosing_inns.lean.groundtruth.choosing_inns_goal
