import SimpleC.SL.SeparationLogic

import Algorithms.rmq.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.rmq.lean.groundtruth.rmq_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance rmq_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def build_safety_wit_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (st0 : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st0 K_pre n_pre)) ,
  ((( &( "idx" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_2 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx <= (n_pre * K_pre))) (PreH6 : (STZeroPrefixBounds st_l idx)) (PreH7 : (STZeroPrefix st_l idx)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((n_pre * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * K_pre)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx <= (n_pre * K_pre))) (PreH6 : (STZeroPrefixBounds st_l idx)) (PreH7 : (STZeroPrefix st_l idx)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((n_pre * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * K_pre)) ”
)

noncomputable def build_safety_wit_2_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx <= (n_pre * K_pre))) (PreH6 : (STZeroPrefixBounds st_l idx)) (PreH7 : (STZeroPrefix st_l idx)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((n_pre * K_pre) <= INT_MAX) ”

noncomputable def build_safety_wit_2_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx <= (n_pre * K_pre))) (PreH6 : (STZeroPrefixBounds st_l idx)) (PreH7 : (STZeroPrefix st_l idx)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (n_pre * K_pre)) ”

noncomputable def build_safety_wit_3 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l idx)) (PreH8 : (STZeroPrefix st_l idx)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_4 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l idx)) (PreH8 : (STZeroPrefix st_l idx)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (idx) ((0 : Int)) (st_l)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((idx + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (idx + 1)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l idx)) (PreH8 : (STZeroPrefix st_l idx)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (idx) ((0 : Int)) (st_l)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((idx + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (idx + 1)) ”
)

noncomputable def build_safety_wit_4_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l idx)) (PreH8 : (STZeroPrefix st_l idx)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (idx) ((0 : Int)) (st_l)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((idx + 1) <= INT_MAX) ”

noncomputable def build_safety_wit_4_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l idx)) (PreH8 : (STZeroPrefix st_l idx)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (idx) ((0 : Int)) (st_l)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= (idx + 1)) ”

noncomputable def build_safety_wit_5 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (STZeroPrefixBounds st_l (n_pre * K_pre))) (PreH5 : (STZeroPrefix st_l (n_pre * K_pre))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_6 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
)

noncomputable def build_safety_wit_6_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ”

noncomputable def build_safety_wit_6_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_7 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : (STBasePrefixBounds n_pre (i + 1))) (PreH7 : (STBasePrefix l st_l K_pre n_pre (i + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_safety_wit_8 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l K_pre n_pre 1)) ,
  ((( &( "half" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_9 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l K_pre n_pre 1)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "half" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def build_safety_wit_10 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l K_pre n_pre 1)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "len" ) )) # Int |-> (2))
  ** ((( &( "half" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_11 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l : (List Int)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_12 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j)) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + len)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j)) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + len)) ”
)

noncomputable def build_safety_wit_12_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j)) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + len) <= INT_MAX) ”

noncomputable def build_safety_wit_12_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j)) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (i + len)) ”

noncomputable def build_safety_wit_13 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((((i * K_pre) + j) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i * K_pre) + j) - 1)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((((i * K_pre) + j) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i * K_pre) + j) - 1)) ”
)

noncomputable def build_safety_wit_13_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((((i * K_pre) + j) - 1) <= INT_MAX) ”

noncomputable def build_safety_wit_13_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (((i * K_pre) + j) - 1)) ”

noncomputable def build_safety_wit_14 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”
)

noncomputable def build_safety_wit_14_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ”

noncomputable def build_safety_wit_14_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”

noncomputable def build_safety_wit_15 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
)

noncomputable def build_safety_wit_15_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ”

noncomputable def build_safety_wit_15_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_16 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_17 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((((i + half) * K_pre) + j) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((i + half) * K_pre) + j) - 1)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((((i + half) * K_pre) + j) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((i + half) * K_pre) + j) - 1)) ”
)

noncomputable def build_safety_wit_17_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((((i + half) * K_pre) + j) - 1) <= INT_MAX) ”

noncomputable def build_safety_wit_17_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= ((((i + half) * K_pre) + j) - 1)) ”

noncomputable def build_safety_wit_18 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((((i + half) * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i + half) * K_pre) + j)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((((i + half) * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i + half) * K_pre) + j)) ”
)

noncomputable def build_safety_wit_18_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((((i + half) * K_pre) + j) <= INT_MAX) ”

noncomputable def build_safety_wit_18_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= (((i + half) * K_pre) + j)) ”

noncomputable def build_safety_wit_19 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((i + half) * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i + half) * K_pre)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((i + half) * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i + half) * K_pre)) ”
)

noncomputable def build_safety_wit_19_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((i + half) * K_pre) <= INT_MAX) ”

noncomputable def build_safety_wit_19_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= ((i + half) * K_pre)) ”

noncomputable def build_safety_wit_20 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i + half) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + half)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i + half) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + half)) ”
)

noncomputable def build_safety_wit_20_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i + half) <= INT_MAX) ”

noncomputable def build_safety_wit_20_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= (i + half)) ”

noncomputable def build_safety_wit_21 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_22 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”
)

noncomputable def build_safety_wit_22_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ”

noncomputable def build_safety_wit_22_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”

noncomputable def build_safety_wit_23 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
)

noncomputable def build_safety_wit_23_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ”

noncomputable def build_safety_wit_23_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_24 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”
)

noncomputable def build_safety_wit_24_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ”

noncomputable def build_safety_wit_24_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”

noncomputable def build_safety_wit_25 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”
)

noncomputable def build_safety_wit_25_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ”

noncomputable def build_safety_wit_25_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_26 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH11 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j)) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1))) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH11 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j)) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1))) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”
)

noncomputable def build_safety_wit_26_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH11 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j)) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1))) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + 1) <= INT_MAX) ”

noncomputable def build_safety_wit_26_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH11 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j)) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1))) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_safety_wit_27 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((len * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len * 2)) ”
) \/
(
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((len * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len * 2)) ”
)

noncomputable def build_safety_wit_27_split_goal_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((len * 2) <= INT_MAX) ”

noncomputable def build_safety_wit_27_split_goal_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (len * 2)) ”

noncomputable def build_safety_wit_28 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def build_safety_wit_29 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> ((len * 2)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def build_entail_wit_1 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (st0 : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st0 K_pre n_pre)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st0)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre * K_pre)) ” &&
  “ (STZeroPrefixBounds st_l (0 : Int)) ” &&
  “ (STZeroPrefix st_l (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (st0 : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st0 K_pre n_pre)) ,
  TT && emp 
|--
  “ (STZeroPrefix st0 (0 : Int)) ” &&
  “ (STZeroPrefixBounds st0 (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre * K_pre)) ”
  &&  emp
)

noncomputable def build_entail_wit_1_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (st0 : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st0 K_pre n_pre)) ,
  (STZeroPrefix st0 (0 : Int))

noncomputable def build_entail_wit_1_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (st0 : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st0 K_pre n_pre)) ,
  (STZeroPrefixBounds st0 (0 : Int))

noncomputable def build_entail_wit_1_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (st0 : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st0 K_pre n_pre)) ,
  ((0 : Int) <= (n_pre * K_pre))

noncomputable def build_entail_wit_2 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (idx) ((0 : Int)) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((0 : Int) <= (idx + 1)) ” &&
  “ ((idx + 1) <= (n_pre * K_pre)) ” &&
  “ (STZeroPrefixBounds st_l (idx + 1)) ” &&
  “ (STZeroPrefix st_l (idx + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  TT && emp 
|--
  “ (STZeroPrefix (replace_Znth (idx) ((0 : Int)) (st_l_2)) (idx + 1)) ” &&
  “ (STZeroPrefixBounds (replace_Znth (idx) ((0 : Int)) (st_l_2)) (idx + 1)) ” &&
  “ (STTableShape (replace_Znth (idx) ((0 : Int)) (st_l_2)) K_pre n_pre) ”
  &&  emp
)

noncomputable def build_entail_wit_2_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  (STZeroPrefix (replace_Znth (idx) ((0 : Int)) (st_l_2)) (idx + 1))

noncomputable def build_entail_wit_2_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  (STZeroPrefixBounds (replace_Znth (idx) ((0 : Int)) (st_l_2)) (idx + 1))

noncomputable def build_entail_wit_2_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  (STTableShape (replace_Znth (idx) ((0 : Int)) (st_l_2)) K_pre n_pre)

noncomputable def build_entail_wit_3 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STZeroPrefixBounds st_l (n_pre * K_pre)) ” &&
  “ (STZeroPrefix st_l (n_pre * K_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  TT && emp 
|--
  “ (STZeroPrefix st_l_2 (n_pre * K_pre)) ” &&
  “ (STZeroPrefixBounds st_l_2 (n_pre * K_pre)) ”
  &&  emp
)

noncomputable def build_entail_wit_3_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  (STZeroPrefix st_l_2 (n_pre * K_pre))

noncomputable def build_entail_wit_3_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (idx : Int) (st_l_2 : (List Int)) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l_2 idx)) (PreH8 : (STZeroPrefix st_l_2 idx)) ,
  (STZeroPrefixBounds st_l_2 (n_pre * K_pre))

noncomputable def build_entail_wit_4 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre))) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBasePrefixBounds n_pre (0 : Int)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre))) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre))) ,
  TT && emp 
|--
  “ (STBasePrefix l st_l_2 K_pre n_pre (0 : Int)) ” &&
  “ (STBasePrefixBounds n_pre (0 : Int)) ”
  &&  emp
)

noncomputable def build_entail_wit_4_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre))) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre))) ,
  (STBasePrefix l st_l_2 K_pre n_pre (0 : Int))

noncomputable def build_entail_wit_4_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre))) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre))) ,
  (STBasePrefixBounds n_pre (0 : Int))

noncomputable def build_entail_wit_5 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (i * K_pre)) ” &&
  “ ((i * K_pre) < (n_pre * K_pre)) ” &&
  “ (STBasePrefixBounds n_pre i) ” &&
  “ (STCellBounds st_l K_pre i (0 : Int)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre i) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  TT && emp 
|--
  “ (STCellBounds st_l_2 K_pre i (0 : Int)) ” &&
  “ ((i * K_pre) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= (i * K_pre)) ” &&
  “ ((0 : Int) <= i) ”
  &&  emp
)

noncomputable def build_entail_wit_5_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STCellBounds st_l_2 K_pre i (0 : Int))

noncomputable def build_entail_wit_5_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  ((i * K_pre) < (n_pre * K_pre))

noncomputable def build_entail_wit_5_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  ((0 : Int) <= (i * K_pre))

noncomputable def build_entail_wit_5_split_goal_4 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  ((0 : Int) <= i)

noncomputable def build_entail_wit_6 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l_2 K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (STBasePrefixBounds n_pre (i + 1)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l_2 K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  TT && emp 
|--
  “ (STBasePrefix l (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)) K_pre n_pre (i + 1)) ” &&
  “ (STBasePrefixBounds n_pre (i + 1)) ” &&
  “ (STTableShape (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)) K_pre n_pre) ”
  &&  emp
)

noncomputable def build_entail_wit_6_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l_2 K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STBasePrefix l (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)) K_pre n_pre (i + 1))

noncomputable def build_entail_wit_6_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l_2 K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STBasePrefixBounds n_pre (i + 1))

noncomputable def build_entail_wit_6_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l_2 K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STTableShape (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)) K_pre n_pre)

noncomputable def build_entail_wit_7 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : (STBasePrefixBounds n_pre (i + 1))) (PreH7 : (STBasePrefix l st_l_2 K_pre n_pre (i + 1))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBasePrefixBounds n_pre (i + 1)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def build_entail_wit_8 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre 1) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre 1) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1) ” &&
  “ (STBuiltBeforeLevelBounds K_pre 1) ”
  &&  emp
)

noncomputable def build_entail_wit_8_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1)

noncomputable def build_entail_wit_8_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (st_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (STBasePrefixBounds n_pre i)) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STBuiltBeforeLevelBounds K_pre 1)

noncomputable def build_entail_wit_9 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= K_pre) ” &&
  “ (1 = (Power2 ((1 - 1)))) ” &&
  “ (2 = (Power2 (1))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre 1) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre 1) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1)) ,
  TT && emp 
|--
  “ (2 = (Power2 (1))) ” &&
  “ (1 = (Power2 ((1 - 1)))) ” &&
  “ (1 <= K_pre) ”
  &&  emp
)

noncomputable def build_entail_wit_9_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1)) ,
  (2 = (Power2 (1)))

noncomputable def build_entail_wit_9_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1)) ,
  (1 = (Power2 ((1 - 1))))

noncomputable def build_entail_wit_9_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1)) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1)) ,
  (1 <= K_pre)

noncomputable def build_entail_wit_10 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j (0 : Int)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  TT && emp 
|--
  “ (STLevelPrefix l st_l_2 K_pre n_pre j (0 : Int)) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j (0 : Int)) ”
  &&  emp
)

noncomputable def build_entail_wit_10_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (STLevelPrefix l st_l_2 K_pre n_pre j (0 : Int))

noncomputable def build_entail_wit_10_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (STLevelPrefixBounds K_pre n_pre j (0 : Int))

noncomputable def build_entail_wit_11 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j i) ” &&
  “ (STCellBounds st_l K_pre i (j - 1)) ” &&
  “ (STCellBounds st_l K_pre (i + half) (j - 1)) ” &&
  “ (STCellBounds st_l K_pre i j) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ” &&
  “ (STCellRangeMax l st_l K_pre i (j - 1)) ” &&
  “ (STCellRangeMax l st_l K_pre (i + half) (j - 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  TT && emp 
|--
  “ (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1)) ” &&
  “ (STCellRangeMax l st_l_2 K_pre i (j - 1)) ” &&
  “ (STCellBounds st_l_2 K_pre i j) ” &&
  “ (STCellBounds st_l_2 K_pre (i + half) (j - 1)) ” &&
  “ (STCellBounds st_l_2 K_pre i (j - 1)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((0 : Int) <= i) ”
  &&  emp
)

noncomputable def build_entail_wit_11_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))

noncomputable def build_entail_wit_11_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STCellRangeMax l st_l_2 K_pre i (j - 1))

noncomputable def build_entail_wit_11_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STCellBounds st_l_2 K_pre i j)

noncomputable def build_entail_wit_11_split_goal_4 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STCellBounds st_l_2 K_pre (i + half) (j - 1))

noncomputable def build_entail_wit_11_split_goal_5 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STCellBounds st_l_2 K_pre i (j - 1))

noncomputable def build_entail_wit_11_split_goal_6 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (((i * K_pre) + j) < (n_pre * K_pre))

noncomputable def build_entail_wit_11_split_goal_7 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((0 : Int) <= ((i * K_pre) + j))

noncomputable def build_entail_wit_11_split_goal_8 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))

noncomputable def build_entail_wit_11_split_goal_9 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))

noncomputable def build_entail_wit_11_split_goal_10 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((((i * K_pre) + j) - 1) < (n_pre * K_pre))

noncomputable def build_entail_wit_11_split_goal_11 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((0 : Int) <= (((i * K_pre) + j) - 1))

noncomputable def build_entail_wit_11_split_goal_12 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((0 : Int) <= i)

noncomputable def build_entail_wit_12 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l_2 : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l_2 K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int))) ” &&
  “ ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)) = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j i) ” &&
  “ (STCellBounds st_l_2 K_pre i (j - 1)) ” &&
  “ (STCellBounds st_l_2 K_pre (i + half) (j - 1)) ” &&
  “ (STCellBounds st_l_2 K_pre i j) ” &&
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l_2 K_pre n_pre j i) ” &&
  “ (STCellRangeMax l st_l_2 K_pre i (j - 1)) ” &&
  “ (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)

noncomputable def build_entail_wit_13_1 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j (i + 1)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) K_pre n_pre j (i + 1)) ” &&
  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) K_pre n_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j (i + 1)) ” &&
  “ (b = (Znth ((((i + half) * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) (0 : Int))) ” &&
  “ (a = (Znth (((i * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) (0 : Int))) ” &&
  “ (STTableShape (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) K_pre n_pre) ”
  &&  emp
)

noncomputable def build_entail_wit_13_1_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) K_pre n_pre j (i + 1))

noncomputable def build_entail_wit_13_1_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) K_pre n_pre j)

noncomputable def build_entail_wit_13_1_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STLevelPrefixBounds K_pre n_pre j (i + 1))

noncomputable def build_entail_wit_13_1_split_goal_4 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (b = (Znth ((((i + half) * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) (0 : Int)))

noncomputable def build_entail_wit_13_1_split_goal_5 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (a = (Znth (((i * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) (0 : Int)))

noncomputable def build_entail_wit_13_1_split_goal_6 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STTableShape (replace_Znth (((i * K_pre) + j)) (a) (st_l_2)) K_pre n_pre)

noncomputable def build_entail_wit_13_2 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j (i + 1)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) K_pre n_pre j (i + 1)) ” &&
  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) K_pre n_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j (i + 1)) ” &&
  “ (b = (Znth ((((i + half) * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) (0 : Int))) ” &&
  “ (a = (Znth (((i * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) (0 : Int))) ” &&
  “ (STTableShape (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) K_pre n_pre) ”
  &&  emp
)

noncomputable def build_entail_wit_13_2_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) K_pre n_pre j (i + 1))

noncomputable def build_entail_wit_13_2_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) K_pre n_pre j)

noncomputable def build_entail_wit_13_2_split_goal_3 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STLevelPrefixBounds K_pre n_pre j (i + 1))

noncomputable def build_entail_wit_13_2_split_goal_4 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (b = (Znth ((((i + half) * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) (0 : Int)))

noncomputable def build_entail_wit_13_2_split_goal_5 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (a = (Znth (((i * K_pre) + j) - 1) (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) (0 : Int)))

noncomputable def build_entail_wit_13_2_split_goal_6 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1))) (PreH22 : (STCellBounds st_l_2 K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l_2 K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half) (j - 1))) ,
  (STTableShape (replace_Znth (((i * K_pre) + j)) (b) (st_l_2)) K_pre n_pre)

noncomputable def build_entail_wit_14 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH11 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j)) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1))) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH15 : (STLevelPrefix l st_l_2 K_pre n_pre j (i + 1))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j (i + 1)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def build_entail_wit_15 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre (j + 1)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1)) ” &&
  “ (STBuiltBeforeLevelBounds K_pre (j + 1)) ”
  &&  emp
)

noncomputable def build_entail_wit_15_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1))

noncomputable def build_entail_wit_15_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : ((i + len) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STBuiltBeforeLevelBounds K_pre (j + 1))

noncomputable def build_entail_wit_16 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= K_pre) ” &&
  “ (len = (Power2 (((j + 1) - 1)))) ” &&
  “ ((len * 2) = (Power2 ((j + 1)))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre (j + 1)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1))) ,
  TT && emp 
|--
  “ ((len * 2) = (Power2 ((j + 1)))) ” &&
  “ (len = (Power2 (((j + 1) - 1)))) ”
  &&  emp
)

noncomputable def build_entail_wit_16_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1))) ,
  ((len * 2) = (Power2 ((j + 1))))

noncomputable def build_entail_wit_16_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l_2 K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1))) ,
  (len = (Power2 (((j + 1) - 1))))

noncomputable def build_return_wit_1 : Prop :=
  (
forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ” &&
  “ (STBuilt l st_l K_pre n_pre) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  TT && emp 
|--
  “ (STBuilt l st_l_2 K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ”
  &&  emp
)

noncomputable def build_return_wit_1_split_goal_1 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (STBuilt l st_l_2 K_pre n_pre)

noncomputable def build_return_wit_1_split_goal_2 : Prop :=
  forall (K_pre : Int) (n_pre : Int) (l : (List Int)) (len : Int) (half : Int) (j : Int) (st_l_2 : (List Int)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l_2 K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j)) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (STBuiltBeforeLevelBounds K_pre K_pre)

noncomputable def build_partial_solve_wit_1 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (idx : Int) (st_l : (List Int)) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx <= (n_pre * K_pre))) (PreH7 : (STZeroPrefixBounds st_l idx)) (PreH8 : (STZeroPrefix st_l idx)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (idx < (n_pre * K_pre)) ” &&
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx <= (n_pre * K_pre)) ” &&
  “ (STZeroPrefixBounds st_l idx) ” &&
  “ (STZeroPrefix st_l idx) ”
  &&  (((st_pre + (idx * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre idx (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_2 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (i * K_pre)) ” &&
  “ ((i * K_pre) < (n_pre * K_pre)) ” &&
  “ (STBasePrefixBounds n_pre i) ” &&
  “ (STCellBounds st_l K_pre i (0 : Int)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre i) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def build_partial_solve_wit_3 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= (i * K_pre))) (PreH7 : ((i * K_pre) < (n_pre * K_pre))) (PreH8 : (STBasePrefixBounds n_pre i)) (PreH9 : (STCellBounds st_l K_pre i (0 : Int))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (i * K_pre)) ” &&
  “ ((i * K_pre) < (n_pre * K_pre)) ” &&
  “ (STBasePrefixBounds n_pre i) ” &&
  “ (STCellBounds st_l K_pre i (0 : Int)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre i) ”
  &&  (((st_pre + ((i * K_pre) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre (i * K_pre) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_4 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j i) ” &&
  “ (STCellBounds st_l K_pre i (j - 1)) ” &&
  “ (STCellBounds st_l K_pre (i + half) (j - 1)) ” &&
  “ (STCellBounds st_l K_pre i j) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ” &&
  “ (STCellRangeMax l st_l K_pre i (j - 1)) ” &&
  “ (STCellRangeMax l st_l K_pre (i + half) (j - 1)) ”
  &&  (((st_pre + ((((i * K_pre) + j) - 1) * sizeof(INT)))) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** (intArray.missing_i st_pre (((i * K_pre) + j) - 1) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_5 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (RMQInputValues l n_pre)) (PreH3 : (STTableShape st_l K_pre n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : ((i + len) <= n_pre)) (PreH10 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH11 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH13 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((i * K_pre) + j))) (PreH15 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j)) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH18 : (STCellBounds st_l K_pre i (j - 1))) (PreH19 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH20 : (STCellBounds st_l K_pre i j)) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH24 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j i) ” &&
  “ (STCellBounds st_l K_pre i (j - 1)) ” &&
  “ (STCellBounds st_l K_pre (i + half) (j - 1)) ” &&
  “ (STCellBounds st_l K_pre i j) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ” &&
  “ (STCellRangeMax l st_l K_pre i (j - 1)) ” &&
  “ (STCellRangeMax l st_l K_pre (i + half) (j - 1)) ”
  &&  (((st_pre + (((((i + half) * K_pre) + j) - 1) * sizeof(INT)))) # Int |-> ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))))
  ** (intArray.missing_i st_pre ((((i + half) * K_pre) + j) - 1) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_6 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (a >= b) ” &&
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j i) ” &&
  “ (STCellBounds st_l K_pre i (j - 1)) ” &&
  “ (STCellBounds st_l K_pre (i + half) (j - 1)) ” &&
  “ (STCellBounds st_l K_pre i j) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ” &&
  “ (STCellRangeMax l st_l K_pre i (j - 1)) ” &&
  “ (STCellRangeMax l st_l K_pre (i + half) (j - 1)) ”
  &&  (((st_pre + (((i * K_pre) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre ((i * K_pre) + j) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_7 : Prop :=
  forall (st_pre : Int) (K_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (a : Int) (b : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (RMQInputValues l n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : ((i + len) <= n_pre)) (PreH11 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH12 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH13 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH14 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((i * K_pre) + j))) (PreH16 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH17 : (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int)))) (PreH18 : (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j)) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i)) (PreH21 : (STCellBounds st_l K_pre i (j - 1))) (PreH22 : (STCellBounds st_l K_pre (i + half) (j - 1))) (PreH23 : (STCellBounds st_l K_pre i j)) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i)) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1))) (PreH27 : (STCellRangeMax l st_l K_pre (i + half) (j - 1))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (a < b) ” &&
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (RMQInputValues l n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (a = (Znth (((i * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (b = (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre j) ” &&
  “ (STLevelPrefixBounds K_pre n_pre j i) ” &&
  “ (STCellBounds st_l K_pre i (j - 1)) ” &&
  “ (STCellBounds st_l K_pre (i + half) (j - 1)) ” &&
  “ (STCellBounds st_l K_pre i j) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ” &&
  “ (STCellRangeMax l st_l K_pre i (j - 1)) ” &&
  “ (STCellRangeMax l st_l K_pre (i + half) (j - 1)) ”
  &&  (((st_pre + (((i * K_pre) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre ((i * K_pre) + j) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def query_safety_wit_1 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((right_pre - left_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right_pre - left_pre) + 1)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((right_pre - left_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right_pre - left_pre) + 1)) ”
)

noncomputable def query_safety_wit_1_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((right_pre - left_pre) + 1) <= INT_MAX) ”

noncomputable def query_safety_wit_1_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= ((right_pre - left_pre) + 1)) ”

noncomputable def query_safety_wit_2 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((right_pre - left_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - left_pre)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((right_pre - left_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - left_pre)) ”
)

noncomputable def query_safety_wit_2_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((right_pre - left_pre) <= INT_MAX) ”

noncomputable def query_safety_wit_2_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (right_pre - left_pre)) ”

noncomputable def query_safety_wit_3 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_safety_wit_4 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "len" ) )) # Int |-> (((right_pre - left_pre) + 1)))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def query_safety_wit_5 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "pow" ) )) # Int |->_)
  ** ((( &( "k" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "len" ) )) # Int |-> (((right_pre - left_pre) + 1)))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_safety_wit_6 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pow * 2)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pow * 2)) ”
)

noncomputable def query_safety_wit_6_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ”

noncomputable def query_safety_wit_6_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (pow * 2)) ”

noncomputable def query_safety_wit_7 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def query_safety_wit_8 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pow * 2)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pow * 2)) ”
)

noncomputable def query_safety_wit_8_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ”

noncomputable def query_safety_wit_8_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (pow * 2)) ”

noncomputable def query_safety_wit_9 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def query_safety_wit_10 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> ((pow * 2)))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> ((pow * 2)))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”
)

noncomputable def query_safety_wit_10_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> ((pow * 2)))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((k + 1) <= INT_MAX) ”

noncomputable def query_safety_wit_10_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> ((pow * 2)))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def query_safety_wit_11 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((left_pre * K_pre) + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left_pre * K_pre) + k)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((left_pre * K_pre) + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left_pre * K_pre) + k)) ”
)

noncomputable def query_safety_wit_11_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((left_pre * K_pre) + k) <= INT_MAX) ”

noncomputable def query_safety_wit_11_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= ((left_pre * K_pre) + k)) ”

noncomputable def query_safety_wit_12 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((left_pre * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_pre * K_pre)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((left_pre * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_pre * K_pre)) ”
)

noncomputable def query_safety_wit_12_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((left_pre * K_pre) <= INT_MAX) ”

noncomputable def query_safety_wit_12_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (left_pre * K_pre)) ”

noncomputable def query_safety_wit_13 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((((right_pre - pow) + 1) * K_pre) + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((right_pre - pow) + 1) * K_pre) + k)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((((right_pre - pow) + 1) * K_pre) + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((right_pre - pow) + 1) * K_pre) + k)) ”
)

noncomputable def query_safety_wit_13_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((((right_pre - pow) + 1) * K_pre) + k) <= INT_MAX) ”

noncomputable def query_safety_wit_13_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((INT_MIN) <= ((((right_pre - pow) + 1) * K_pre) + k)) ”

noncomputable def query_safety_wit_14 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((((right_pre - pow) + 1) * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((right_pre - pow) + 1) * K_pre)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((((right_pre - pow) + 1) * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((right_pre - pow) + 1) * K_pre)) ”
)

noncomputable def query_safety_wit_14_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((((right_pre - pow) + 1) * K_pre) <= INT_MAX) ”

noncomputable def query_safety_wit_14_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((INT_MIN) <= (((right_pre - pow) + 1) * K_pre)) ”

noncomputable def query_safety_wit_15 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((right_pre - pow) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right_pre - pow) + 1)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((right_pre - pow) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right_pre - pow) + 1)) ”
)

noncomputable def query_safety_wit_15_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((right_pre - pow) + 1) <= INT_MAX) ”

noncomputable def query_safety_wit_15_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((INT_MIN) <= ((right_pre - pow) + 1)) ”

noncomputable def query_safety_wit_16 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((right_pre - pow) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - pow)) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((right_pre - pow) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - pow)) ”
)

noncomputable def query_safety_wit_16_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((right_pre - pow) <= INT_MAX) ”

noncomputable def query_safety_wit_16_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((INT_MIN) <= (right_pre - pow)) ”

noncomputable def query_safety_wit_17 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_entail_wit_1 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (((right_pre - left_pre) + 1) = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ” &&
  “ (STBuilt l st_l K_pre n_pre) ” &&
  “ (QueryLogBounds K_pre n_pre ((right_pre - left_pre) + 1) (0 : Int) 1) ” &&
  “ (QueryLogLoopState ((right_pre - left_pre) + 1) (0 : Int) 1) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  TT && emp 
|--
  “ (QueryLogLoopState ((right_pre - left_pre) + 1) (0 : Int) 1) ” &&
  “ (QueryLogBounds K_pre n_pre ((right_pre - left_pre) + 1) (0 : Int) 1) ”
  &&  emp
)

noncomputable def query_entail_wit_1_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  (QueryLogLoopState ((right_pre - left_pre) + 1) (0 : Int) 1)

noncomputable def query_entail_wit_1_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre)) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH6 : (STBuilt l st_l K_pre n_pre)) ,
  (QueryLogBounds K_pre n_pre ((right_pre - left_pre) + 1) (0 : Int) 1)

noncomputable def query_entail_wit_2 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ” &&
  “ (STBuilt l st_l K_pre n_pre) ” &&
  “ (QueryLogBounds K_pre n_pre len (k + 1) (pow * 2)) ” &&
  “ (QueryLogLoopState len (k + 1) (pow * 2)) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  TT && emp 
|--
  “ (QueryLogLoopState ((right_pre - left_pre) + 1) (k + 1) (pow * 2)) ” &&
  “ (QueryLogBounds K_pre n_pre ((right_pre - left_pre) + 1) (k + 1) (pow * 2)) ”
  &&  emp
)

noncomputable def query_entail_wit_2_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (QueryLogLoopState ((right_pre - left_pre) + 1) (k + 1) (pow * 2))

noncomputable def query_entail_wit_2_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (QueryLogBounds K_pre n_pre ((right_pre - left_pre) + 1) (k + 1) (pow * 2))

noncomputable def query_entail_wit_3 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ” &&
  “ (STBuilt l st_l K_pre n_pre) ” &&
  “ (QueryLogBounds K_pre n_pre len k pow) ” &&
  “ (QueryLogFinalState len k pow) ” &&
  “ ((0 : Int) <= ((left_pre * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ (STCellBounds st_l K_pre left_pre k) ” &&
  “ (STCellBounds st_l K_pre ((right_pre - pow) + 1) k) ” &&
  “ (STCellRangeMax l st_l K_pre left_pre k) ” &&
  “ (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  TT && emp 
|--
  “ (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k) ” &&
  “ (STCellRangeMax l st_l K_pre left_pre k) ” &&
  “ (STCellBounds st_l K_pre ((right_pre - pow) + 1) k) ” &&
  “ (STCellBounds st_l K_pre left_pre k) ” &&
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((left_pre * K_pre) + k)) ” &&
  “ (QueryLogFinalState ((right_pre - left_pre) + 1) k pow) ”
  &&  emp
)

noncomputable def query_entail_wit_3_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)

noncomputable def query_entail_wit_3_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (STCellRangeMax l st_l K_pre left_pre k)

noncomputable def query_entail_wit_3_split_goal_3 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)

noncomputable def query_entail_wit_3_split_goal_4 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (STCellBounds st_l K_pre left_pre k)

noncomputable def query_entail_wit_3_split_goal_5 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))

noncomputable def query_entail_wit_3_split_goal_6 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))

noncomputable def query_entail_wit_3_split_goal_7 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (((left_pre * K_pre) + k) < (n_pre * K_pre))

noncomputable def query_entail_wit_3_split_goal_8 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  ((0 : Int) <= ((left_pre * K_pre) + k))

noncomputable def query_entail_wit_3_split_goal_9 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (k : Int) (pow : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH8 : (STBuilt l st_l K_pre n_pre)) (PreH9 : (QueryLogBounds K_pre n_pre len k pow)) (PreH10 : (QueryLogLoopState len k pow)) ,
  (QueryLogFinalState ((right_pre - left_pre) + 1) k pow)

noncomputable def query_entail_wit_4 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ ((Znth ((left_pre * K_pre) + k) st_l (0 : Int)) = (Znth ((left_pre * K_pre) + k) st_l (0 : Int))) ” &&
  “ ((Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)) = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int))) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ” &&
  “ (STBuilt l st_l K_pre n_pre) ” &&
  “ (QueryLogBounds K_pre n_pre len k pow) ” &&
  “ (QueryLogFinalState len k pow) ” &&
  “ (STCellBounds st_l K_pre left_pre k) ” &&
  “ (STCellBounds st_l K_pre ((right_pre - pow) + 1) k) ” &&
  “ (STCellRangeMax l st_l K_pre left_pre k) ” &&
  “ (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def query_entail_wit_5 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH8 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH10 : (STBuilt l st_l K_pre n_pre)) (PreH11 : (QueryLogBounds K_pre n_pre len k pow)) (PreH12 : (QueryLogFinalState len k pow)) (PreH13 : (STCellBounds st_l K_pre left_pre k)) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int))) ” &&
  “ (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int))) ” &&
  “ (QueryLogBounds K_pre n_pre len k pow) ” &&
  “ (QueryLogFinalState len k pow) ” &&
  “ (RangeMaxValue l left_pre (right_pre + 1) a) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH8 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH10 : (STBuilt l st_l K_pre n_pre)) (PreH11 : (QueryLogBounds K_pre n_pre len k pow)) (PreH12 : (QueryLogFinalState len k pow)) (PreH13 : (STCellBounds st_l K_pre left_pre k)) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) a) ”
  &&  emp
)

noncomputable def query_entail_wit_5_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH8 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH10 : (STBuilt l st_l K_pre n_pre)) (PreH11 : (QueryLogBounds K_pre n_pre len k pow)) (PreH12 : (QueryLogFinalState len k pow)) (PreH13 : (STCellBounds st_l K_pre left_pre k)) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  (RangeMaxValue l left_pre (right_pre + 1) a)

noncomputable def query_entail_wit_6 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH8 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH10 : (STBuilt l st_l K_pre n_pre)) (PreH11 : (QueryLogBounds K_pre n_pre len k pow)) (PreH12 : (QueryLogFinalState len k pow)) (PreH13 : (STCellBounds st_l K_pre left_pre k)) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int))) ” &&
  “ (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int))) ” &&
  “ (QueryLogBounds K_pre n_pre len k pow) ” &&
  “ (QueryLogFinalState len k pow) ” &&
  “ (RangeMaxValue l left_pre (right_pre + 1) b) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH8 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH10 : (STBuilt l st_l K_pre n_pre)) (PreH11 : (QueryLogBounds K_pre n_pre len k pow)) (PreH12 : (QueryLogFinalState len k pow)) (PreH13 : (STCellBounds st_l K_pre left_pre k)) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) b) ”
  &&  emp
)

noncomputable def query_entail_wit_6_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre)) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH4 : (len = ((right_pre - left_pre) + 1))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre)) (PreH7 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH8 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH10 : (STBuilt l st_l K_pre n_pre)) (PreH11 : (QueryLogBounds K_pre n_pre len k pow)) (PreH12 : (QueryLogFinalState len k pow)) (PreH13 : (STCellBounds st_l K_pre left_pre k)) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  (RangeMaxValue l left_pre (right_pre + 1) b)

noncomputable def query_return_wit_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH7 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : (RangeMaxValue l left_pre (right_pre + 1) b)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) b) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def query_return_wit_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (a : Int) (k : Int) (b : Int) (pow : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (a = (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))) (PreH7 : (b = (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : (RangeMaxValue l left_pre (right_pre + 1) a)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) a) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def query_partial_solve_wit_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ” &&
  “ (STBuilt l st_l K_pre n_pre) ” &&
  “ (QueryLogBounds K_pre n_pre len k pow) ” &&
  “ (QueryLogFinalState len k pow) ” &&
  “ ((0 : Int) <= ((left_pre * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ (STCellBounds st_l K_pre left_pre k) ” &&
  “ (STCellBounds st_l K_pre ((right_pre - pow) + 1) k) ” &&
  “ (STCellRangeMax l st_l K_pre left_pre k) ” &&
  “ (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k) ”
  &&  (((st_pre + (((left_pre * K_pre) + k) * sizeof(INT)))) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** (intArray.missing_i st_pre ((left_pre * K_pre) + k) (0 : Int) (n_pre * K_pre) st_l)

noncomputable def query_partial_solve_wit_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (K_pre : Int) (n_pre : Int) (st_pre : Int) (st_l : (List Int)) (l : (List Int)) (len : Int) (pow : Int) (k : Int) (PreH1 : (RMQSizeSafe n_pre K_pre)) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre)) (PreH3 : (len = ((right_pre - left_pre) + 1))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre)) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre)) (PreH7 : (STBuilt l st_l K_pre n_pre)) (PreH8 : (QueryLogBounds K_pre n_pre len k pow)) (PreH9 : (QueryLogFinalState len k pow)) (PreH10 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH11 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH12 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH13 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH14 : (STCellBounds st_l K_pre left_pre k)) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow) + 1) k)) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k)) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RMQSizeSafe n_pre K_pre) ” &&
  “ (QueryIntervalBounds n_pre left_pre right_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (STTableShape st_l K_pre n_pre) ” &&
  “ (STBuiltBeforeLevelBounds K_pre K_pre) ” &&
  “ (STBuilt l st_l K_pre n_pre) ” &&
  “ (QueryLogBounds K_pre n_pre len k pow) ” &&
  “ (QueryLogFinalState len k pow) ” &&
  “ ((0 : Int) <= ((left_pre * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ (STCellBounds st_l K_pre left_pre k) ” &&
  “ (STCellBounds st_l K_pre ((right_pre - pow) + 1) k) ” &&
  “ (STCellRangeMax l st_l K_pre left_pre k) ” &&
  “ (STCellRangeMax l st_l K_pre ((right_pre - pow) + 1) k) ”
  &&  (((st_pre + (((((right_pre - pow) + 1) * K_pre) + k) * sizeof(INT)))) # Int |-> ((Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int))))
  ** (intArray.missing_i st_pre ((((right_pre - pow) + 1) * K_pre) + k) (0 : Int) (n_pre * K_pre) st_l)


structure VC_Correct : Type where
  proof_of_build_safety_wit_1 : build_safety_wit_1
  proof_of_build_safety_wit_3 : build_safety_wit_3
  proof_of_build_safety_wit_5 : build_safety_wit_5
  proof_of_build_safety_wit_7 : build_safety_wit_7
  proof_of_build_safety_wit_8 : build_safety_wit_8
  proof_of_build_safety_wit_9 : build_safety_wit_9
  proof_of_build_safety_wit_10 : build_safety_wit_10
  proof_of_build_safety_wit_11 : build_safety_wit_11
  proof_of_build_safety_wit_16 : build_safety_wit_16
  proof_of_build_safety_wit_21 : build_safety_wit_21
  proof_of_build_safety_wit_28 : build_safety_wit_28
  proof_of_build_safety_wit_29 : build_safety_wit_29
  proof_of_build_entail_wit_7 : build_entail_wit_7
  proof_of_build_entail_wit_12 : build_entail_wit_12
  proof_of_build_entail_wit_14 : build_entail_wit_14
  proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1
  proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2
  proof_of_build_partial_solve_wit_3 : build_partial_solve_wit_3
  proof_of_build_partial_solve_wit_4 : build_partial_solve_wit_4
  proof_of_build_partial_solve_wit_5 : build_partial_solve_wit_5
  proof_of_build_partial_solve_wit_6 : build_partial_solve_wit_6
  proof_of_build_partial_solve_wit_7 : build_partial_solve_wit_7
  proof_of_query_safety_wit_3 : query_safety_wit_3
  proof_of_query_safety_wit_4 : query_safety_wit_4
  proof_of_query_safety_wit_5 : query_safety_wit_5
  proof_of_query_safety_wit_7 : query_safety_wit_7
  proof_of_query_safety_wit_9 : query_safety_wit_9
  proof_of_query_safety_wit_17 : query_safety_wit_17
  proof_of_query_entail_wit_4 : query_entail_wit_4
  proof_of_query_return_wit_1 : query_return_wit_1
  proof_of_query_return_wit_2 : query_return_wit_2
  proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1
  proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2
  proof_of_build_safety_wit_2 : build_safety_wit_2
  proof_of_build_safety_wit_4 : build_safety_wit_4
  proof_of_build_safety_wit_6 : build_safety_wit_6
  proof_of_build_safety_wit_12 : build_safety_wit_12
  proof_of_build_safety_wit_13 : build_safety_wit_13
  proof_of_build_safety_wit_14 : build_safety_wit_14
  proof_of_build_safety_wit_15 : build_safety_wit_15
  proof_of_build_safety_wit_17 : build_safety_wit_17
  proof_of_build_safety_wit_18 : build_safety_wit_18
  proof_of_build_safety_wit_19 : build_safety_wit_19
  proof_of_build_safety_wit_20 : build_safety_wit_20
  proof_of_build_safety_wit_22 : build_safety_wit_22
  proof_of_build_safety_wit_23 : build_safety_wit_23
  proof_of_build_safety_wit_24 : build_safety_wit_24
  proof_of_build_safety_wit_25 : build_safety_wit_25
  proof_of_build_safety_wit_26 : build_safety_wit_26
  proof_of_build_safety_wit_27 : build_safety_wit_27
  proof_of_build_entail_wit_1 : build_entail_wit_1
  proof_of_build_entail_wit_2 : build_entail_wit_2
  proof_of_build_entail_wit_3 : build_entail_wit_3
  proof_of_build_entail_wit_4 : build_entail_wit_4
  proof_of_build_entail_wit_5 : build_entail_wit_5
  proof_of_build_entail_wit_6 : build_entail_wit_6
  proof_of_build_entail_wit_8 : build_entail_wit_8
  proof_of_build_entail_wit_9 : build_entail_wit_9
  proof_of_build_entail_wit_10 : build_entail_wit_10
  proof_of_build_entail_wit_11 : build_entail_wit_11
  proof_of_build_entail_wit_13_1 : build_entail_wit_13_1
  proof_of_build_entail_wit_13_2 : build_entail_wit_13_2
  proof_of_build_entail_wit_15 : build_entail_wit_15
  proof_of_build_entail_wit_16 : build_entail_wit_16
  proof_of_build_return_wit_1 : build_return_wit_1
  proof_of_query_safety_wit_1 : query_safety_wit_1
  proof_of_query_safety_wit_2 : query_safety_wit_2
  proof_of_query_safety_wit_6 : query_safety_wit_6
  proof_of_query_safety_wit_8 : query_safety_wit_8
  proof_of_query_safety_wit_10 : query_safety_wit_10
  proof_of_query_safety_wit_11 : query_safety_wit_11
  proof_of_query_safety_wit_12 : query_safety_wit_12
  proof_of_query_safety_wit_13 : query_safety_wit_13
  proof_of_query_safety_wit_14 : query_safety_wit_14
  proof_of_query_safety_wit_15 : query_safety_wit_15
  proof_of_query_safety_wit_16 : query_safety_wit_16
  proof_of_query_entail_wit_1 : query_entail_wit_1
  proof_of_query_entail_wit_2 : query_entail_wit_2
  proof_of_query_entail_wit_3 : query_entail_wit_3
  proof_of_query_entail_wit_5 : query_entail_wit_5
  proof_of_query_entail_wit_6 : query_entail_wit_6

end Algorithms.rmq.lean.groundtruth.rmq_goal
