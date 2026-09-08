import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sliding_window_maximum_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def maxSlidingWindow_safety_wit_1 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  ((( &( "head" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_2 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  ((( &( "tail" ) )) # Int |->_)
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_3 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  ((( &( "out_idx" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_4 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "out_idx" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "tail" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_5 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail i)) (PreH20 : (SWMQueueDropLoopState l q_l head tail i k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) ,
  (intArray.full q_pre n_pre q_l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ ((i - k_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - k_pre)) ”

noncomputable def maxSlidingWindow_safety_wit_6 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : ((Znth head q_l (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueStorageSafe l q_l head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) ,
  (intArray.full q_pre n_pre q_l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ ((head + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (head + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_7 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail i)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def maxSlidingWindow_safety_wit_8 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail i)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def maxSlidingWindow_safety_wit_9 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueStorageSafe l q_l head tail i)) (PreH21 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full q_pre n_pre q_l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def maxSlidingWindow_safety_wit_10 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH18 : (SWMQueueStorageSafe l q_l head tail i)) (PreH19 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH20 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  (intArray.full q_pre n_pre (replace_Znth (tail) (i) (q_l)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ ((tail + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_11 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH18 : (SWMQueueStorageSafe l q_l head tail (i + 1))) (PreH19 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH20 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ ((k_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k_pre - 1)) ”

noncomputable def maxSlidingWindow_safety_wit_12 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH18 : (SWMQueueStorageSafe l q_l head tail (i + 1))) (PreH19 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH20 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def maxSlidingWindow_safety_wit_13 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (out_idx = ((i - k_pre) + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx < ((n_pre - k_pre) + 1))) (PreH14 : (SWMInputSafe l n_pre k_pre)) (PreH15 : (SWMOutputPrefixShape l k_pre (out_idx + 1) out_l)) (PreH16 : (SWMOutputPrefix l k_pre (out_idx + 1) out_l)) (PreH17 : (SWMQueueStorageSafe l q_l head tail (i + 1))) (PreH18 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH19 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) (out_idx + 1) out_l)
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ ((out_idx + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (out_idx + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_14 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : (((i + 1) < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1)))) (PreH15 : ((k_pre <= (i + 1)) -> (head < tail))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail (i + 1))) (PreH20 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def maxSlidingWindow_entail_wit_1 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q0)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - k_pre) + 1)) ” &&
  “ (((0 : Int) < k_pre) -> ((0 : Int) = (0 : Int))) ” &&
  “ ((k_pre <= (0 : Int)) -> ((0 : Int) = (((0 : Int) - k_pre) + 1))) ” &&
  “ ((k_pre <= (0 : Int)) -> ((0 : Int) < (0 : Int))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre (0 : Int) out_l) ” &&
  “ (SWMOutputPrefix l k_pre (0 : Int) out_l) ” &&
  “ (SWMQueueStorageSafe l q_l (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ (SWMQueueState l q_l (0 : Int) (0 : Int) (0 : Int) k_pre) ” &&
  “ forall (pos : Int) , ((((0 : Int) <= pos) ∧ (pos < (0 : Int))) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) (0 : Int) out_l)
  ** (intArray.undef_seg out_pre (0 : Int) ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  TT && emp 
|--
  “ forall (pos : Int) , ((((0 : Int) <= pos) ∧ (pos < (0 : Int))) -> (((0 : Int) <= (Znth pos q0 (0 : Int))) ∧ ((Znth pos q0 (0 : Int)) < n_pre))) ” &&
  “ (SWMQueueState l q0 (0 : Int) (0 : Int) (0 : Int) k_pre) ” &&
  “ (SWMQueueStorageSafe l q0 (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ (SWMOutputPrefix l k_pre (0 : Int) (@List.nil Int)) ” &&
  “ (SWMOutputPrefixShape l k_pre (0 : Int) (@List.nil Int)) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  forall (pos : Int) , ((((0 : Int) <= pos) ∧ (pos < (0 : Int))) -> (((0 : Int) <= (Znth pos q0 (0 : Int))) ∧ ((Znth pos q0 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_1_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  (SWMQueueState l q0 (0 : Int) (0 : Int) (0 : Int) k_pre)

noncomputable def maxSlidingWindow_entail_wit_1_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  (SWMQueueStorageSafe l q0 (0 : Int) (0 : Int) (0 : Int))

noncomputable def maxSlidingWindow_entail_wit_1_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  (SWMOutputPrefix l k_pre (0 : Int) (@List.nil Int))

noncomputable def maxSlidingWindow_entail_wit_1_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (q0 : (List Int)) (l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : (SWMInputSafe l n_pre k_pre)) ,
  (SWMOutputPrefixShape l k_pre (0 : Int) (@List.nil Int))

noncomputable def maxSlidingWindow_entail_wit_2 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueueDropLoopState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ” &&
  “ (SWMQueueDropLoopState l q_l_2 head tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueDropLoopState l q_l_2 head tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_3 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full q_pre n_pre q_l_2)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (head + 1)) ” &&
  “ ((head + 1) <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l (head + 1) tail i) ” &&
  “ (SWMQueueDropLoopState l q_l (head + 1) tail i k_pre) ” &&
  “ forall (pos : Int) , ((((head + 1) <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (SWMQueueDropLoopState l q_l_2 (head + 1) tail i k_pre) ” &&
  “ (SWMQueueStorageSafe l q_l_2 (head + 1) tail i) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_3_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueDropLoopState l q_l_2 (head + 1) tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_3_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueStorageSafe l q_l_2 (head + 1) tail i)

noncomputable def maxSlidingWindow_entail_wit_4_1 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueueAfterDrop l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ” &&
  “ (SWMQueueAfterDrop l q_l_2 head tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_4_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_4_1_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueAfterDrop l q_l_2 head tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_4_2 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full q_pre n_pre q_l_2)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueueAfterDrop l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ” &&
  “ (SWMQueueAfterDrop l q_l_2 head tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_4_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_4_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueAfterDrop l q_l_2 head tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_5 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ” &&
  “ (SWMQueuePendingState l q_l_2 head tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_5_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_5_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueuePendingState l q_l_2 head tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_6 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full q_pre n_pre q_l_2)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= (tail - 1)) ” &&
  “ ((tail - 1) <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head (tail - 1) i) ” &&
  “ (SWMQueuePendingState l q_l head (tail - 1) i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < (tail - 1))) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < (tail - 1)) -> (((((0 : Int) <= ((tail - 1) - 1)) ∧ (((tail - 1) - 1) < n_pre)) ∧ ((0 : Int) <= (Znth ((tail - 1) - 1) q_l (0 : Int)))) ∧ ((Znth ((tail - 1) - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (SWMQueuePendingState l q_l_2 head (tail - 1) i k_pre) ” &&
  “ (SWMQueueStorageSafe l q_l_2 head (tail - 1) i) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_6_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueuePendingState l q_l_2 head (tail - 1) i k_pre)

noncomputable def maxSlidingWindow_entail_wit_6_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueStorageSafe l q_l_2 head (tail - 1) i)

noncomputable def maxSlidingWindow_entail_wit_7_1 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_7_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_7_2 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full q_pre n_pre q_l_2)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_7_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_8 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  (intArray.full q_pre n_pre (replace_Znth (tail) (i) (q_l_2)))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < (tail + 1)) ” &&
  “ ((tail + 1) <= (i + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head (tail + 1) (i + 1)) ” &&
  “ (SWMQueueState l q_l head (tail + 1) (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < (tail + 1))) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < (tail + 1))) -> (((0 : Int) <= (Znth pos (replace_Znth (tail) (i) (q_l_2)) (0 : Int))) ∧ ((Znth pos (replace_Znth (tail) (i) (q_l_2)) (0 : Int)) < n_pre))) ” &&
  “ (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1) k_pre) ” &&
  “ (SWMQueueStorageSafe l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1)) ” &&
  “ ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_8_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < (tail + 1))) -> (((0 : Int) <= (Znth pos (replace_Znth (tail) (i) (q_l_2)) (0 : Int))) ∧ ((Znth pos (replace_Znth (tail) (i) (q_l_2)) (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_8_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1) k_pre)

noncomputable def maxSlidingWindow_entail_wit_8_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  (SWMQueueStorageSafe l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1))

noncomputable def maxSlidingWindow_entail_wit_8_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH18 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH19 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH20 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre)

noncomputable def maxSlidingWindow_entail_wit_9 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int))) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_9_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))

noncomputable def maxSlidingWindow_entail_wit_9_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_10 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  (intArray.seg out_pre (0 : Int) (out_idx + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre (out_idx + 1) out_l) ” &&
  “ (SWMOutputPrefix l k_pre (out_idx + 1) out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) (out_idx + 1) out_l)
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ” &&
  “ (SWMOutputPrefix l k_pre (((i - k_pre) + 1) + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int)))) ” &&
  “ (SWMOutputPrefixShape l k_pre (((i - k_pre) + 1) + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int)))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_10_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_10_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  (SWMOutputPrefix l k_pre (((i - k_pre) + 1) + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))

noncomputable def maxSlidingWindow_entail_wit_10_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  (SWMOutputPrefixShape l k_pre (((i - k_pre) + 1) + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))

noncomputable def maxSlidingWindow_entail_wit_11_1 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (out_idx = ((i - k_pre) + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx < ((n_pre - k_pre) + 1))) (PreH14 : (SWMInputSafe l n_pre k_pre)) (PreH15 : (SWMOutputPrefixShape l k_pre (out_idx + 1) out_l_2)) (PreH16 : (SWMOutputPrefix l k_pre (out_idx + 1) out_l_2)) (PreH17 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH18 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH19 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) (out_idx + 1) out_l_2)
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ ((0 : Int) <= (out_idx + 1)) ” &&
  “ ((out_idx + 1) <= ((n_pre - k_pre) + 1)) ” &&
  “ (((i + 1) < k_pre) -> ((out_idx + 1) = (0 : Int))) ” &&
  “ ((k_pre <= (i + 1)) -> ((out_idx + 1) = (((i + 1) - k_pre) + 1))) ” &&
  “ ((k_pre <= (i + 1)) -> (head < tail)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre (out_idx + 1) out_l) ” &&
  “ (SWMOutputPrefix l k_pre (out_idx + 1) out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) (out_idx + 1) out_l)
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (out_idx = ((i - k_pre) + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx < ((n_pre - k_pre) + 1))) (PreH14 : (SWMInputSafe l n_pre k_pre)) (PreH15 : (SWMOutputPrefixShape l k_pre (out_idx + 1) out_l_2)) (PreH16 : (SWMOutputPrefix l k_pre (out_idx + 1) out_l_2)) (PreH17 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH18 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH19 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_11_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (out_idx = ((i - k_pre) + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx < ((n_pre - k_pre) + 1))) (PreH14 : (SWMInputSafe l n_pre k_pre)) (PreH15 : (SWMOutputPrefixShape l k_pre (out_idx + 1) out_l_2)) (PreH16 : (SWMOutputPrefix l k_pre (out_idx + 1) out_l_2)) (PreH17 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH18 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH19 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_11_2 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i < (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ (((i + 1) < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1))) ” &&
  “ ((k_pre <= (i + 1)) -> (head < tail)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i < (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_11_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i < (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_12 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : (((i + 1) < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1)))) (PreH15 : ((k_pre <= (i + 1)) -> (head < tail))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ (((i + 1) < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1))) ” &&
  “ ((k_pre <= (i + 1)) -> (head < tail)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : (((i + 1) < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1)))) (PreH15 : ((k_pre <= (i + 1)) -> (head < tail))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_12_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : (((i + 1) < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1)))) (PreH15 : ((k_pre <= (i + 1)) -> (head < tail))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH19 : (SWMQueueStorageSafe l q_l_2 head tail (i + 1))) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : forall (pos_2 : Int) , (((head <= pos_2) ∧ (pos_2 < tail)) -> (((0 : Int) <= (Znth pos_2 q_l_2 (0 : Int))) ∧ ((Znth pos_2 q_l_2 (0 : Int)) < n_pre)))) ,
  forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_13 : Prop :=
  (
forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= n_pre) ” &&
  “ (out_idx = ((n_pre - k_pre) + 1)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SlidingWindowMaximum l k_pre out_l) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.full out_pre ((n_pre - k_pre) + 1) out_l)
  ** (intArray.full q_pre n_pre q_l)
) \/
(
forall (out_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l_2)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueStorageSafe l q_l_2 head tail i)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l_2 (0 : Int))) ∧ ((Znth pos q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.seg out_pre (0 : Int) out_idx out_l_2)
|--
  EX out_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l_2)) = n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= n_pre) ” &&
  “ (out_idx = ((n_pre - k_pre) + 1)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SlidingWindowMaximum l k_pre out_l) ”
  &&  (intArray.full out_pre ((n_pre - k_pre) + 1) out_l)
)

noncomputable def maxSlidingWindow_return_wit_1 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= head)) (PreH7 : (head <= tail)) (PreH8 : (tail <= n_pre)) (PreH9 : (out_idx = ((n_pre - k_pre) + 1))) (PreH10 : (SWMInputSafe l n_pre k_pre)) (PreH11 : (SlidingWindowMaximum l k_pre out_l_2)) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full out_pre ((n_pre - k_pre) + 1) out_l_2)
  ** (intArray.full q_pre n_pre q_l_2)
|--
  EX q_l : (List Int), EX out_l : (List Int),
  “ (SlidingWindowMaximum l k_pre out_l) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.full out_pre ((n_pre - k_pre) + 1) out_l)
  ** (intArray.full q_pre n_pre q_l)

noncomputable def maxSlidingWindow_partial_solve_wit_1 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail i)) (PreH20 : (SWMQueueDropLoopState l q_l head tail i k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueueDropLoopState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ”
  &&  (((q_pre + (head * sizeof(INT)))) # Int |-> ((Znth head q_l (0 : Int))))
  ** (intArray.missing_i q_pre head (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))

noncomputable def maxSlidingWindow_partial_solve_wit_2 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail i)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((q_pre + ((tail - 1) * sizeof(INT)))) # Int |-> ((Znth (tail - 1) q_l (0 : Int))))
  ** (intArray.missing_i q_pre (tail - 1) (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))

noncomputable def maxSlidingWindow_partial_solve_wit_3 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail i)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full q_pre n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((nums_pre + ((Znth (tail - 1) q_l (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int))))
  ** (intArray.missing_i nums_pre (Znth (tail - 1) q_l (0 : Int)) (0 : Int) n_pre l)
  ** (intArray.full q_pre n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))

noncomputable def maxSlidingWindow_partial_solve_wit_4 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (SWMInputSafe l n_pre k_pre)) (PreH17 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueStorageSafe l q_l head tail i)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full q_pre n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) n_pre l)
  ** (intArray.full q_pre n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))

noncomputable def maxSlidingWindow_partial_solve_wit_5 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (SWMInputSafe l n_pre k_pre)) (PreH16 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH18 : (SWMQueueStorageSafe l q_l head tail i)) (PreH19 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH20 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH21 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail i) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ” &&
  “ ((head < tail) -> ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) ”
  &&  (((q_pre + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i q_pre tail (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))

noncomputable def maxSlidingWindow_partial_solve_wit_6 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l (0 : Int)))) (PreH13 : ((Znth head q_l (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueStorageSafe l q_l head tail (i + 1))) (PreH21 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full q_pre n_pre q_l)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (((q_pre + (head * sizeof(INT)))) # Int |-> ((Znth head q_l (0 : Int))))
  ** (intArray.missing_i q_pre head (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))

noncomputable def maxSlidingWindow_partial_solve_wit_7 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l (0 : Int)))) (PreH13 : ((Znth head q_l (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueStorageSafe l q_l head tail (i + 1))) (PreH21 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int)))) ,
  (intArray.full q_pre n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (((nums_pre + ((Znth head q_l (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth head q_l (0 : Int)) l (0 : Int))))
  ** (intArray.missing_i nums_pre (Znth head q_l (0 : Int)) (0 : Int) n_pre l)
  ** (intArray.full q_pre n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))

noncomputable def maxSlidingWindow_partial_solve_wit_8 : Prop :=
  forall (q_pre : Int) (out_pre : Int) (k_pre : Int) (n_pre : Int) (nums_pre : Int) (l : (List Int)) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l (0 : Int)))) (PreH13 : ((Znth head q_l (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (SWMInputSafe l n_pre k_pre)) (PreH18 : (SWMOutputPrefixShape l k_pre out_idx out_l)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueStorageSafe l q_l head tail (i + 1))) (PreH21 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH22 : forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre)))) (PreH23 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full q_pre n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (SWMInputSafe l n_pre k_pre) ” &&
  “ (SWMOutputPrefixShape l k_pre out_idx out_l) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueStorageSafe l q_l head tail (i + 1)) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ forall (pos : Int) , (((head <= pos) ∧ (pos < tail)) -> (((0 : Int) <= (Znth pos q_l (0 : Int))) ∧ ((Znth pos q_l (0 : Int)) < n_pre))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (((out_pre + (out_idx * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.full q_pre n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)


structure VC_Correct : Type where
  proof_of_maxSlidingWindow_safety_wit_1 : maxSlidingWindow_safety_wit_1
  proof_of_maxSlidingWindow_safety_wit_2 : maxSlidingWindow_safety_wit_2
  proof_of_maxSlidingWindow_safety_wit_3 : maxSlidingWindow_safety_wit_3
  proof_of_maxSlidingWindow_safety_wit_4 : maxSlidingWindow_safety_wit_4
  proof_of_maxSlidingWindow_safety_wit_5 : maxSlidingWindow_safety_wit_5
  proof_of_maxSlidingWindow_safety_wit_6 : maxSlidingWindow_safety_wit_6
  proof_of_maxSlidingWindow_safety_wit_7 : maxSlidingWindow_safety_wit_7
  proof_of_maxSlidingWindow_safety_wit_8 : maxSlidingWindow_safety_wit_8
  proof_of_maxSlidingWindow_safety_wit_9 : maxSlidingWindow_safety_wit_9
  proof_of_maxSlidingWindow_safety_wit_10 : maxSlidingWindow_safety_wit_10
  proof_of_maxSlidingWindow_safety_wit_11 : maxSlidingWindow_safety_wit_11
  proof_of_maxSlidingWindow_safety_wit_12 : maxSlidingWindow_safety_wit_12
  proof_of_maxSlidingWindow_safety_wit_13 : maxSlidingWindow_safety_wit_13
  proof_of_maxSlidingWindow_safety_wit_14 : maxSlidingWindow_safety_wit_14
  proof_of_maxSlidingWindow_return_wit_1 : maxSlidingWindow_return_wit_1
  proof_of_maxSlidingWindow_partial_solve_wit_1 : maxSlidingWindow_partial_solve_wit_1
  proof_of_maxSlidingWindow_partial_solve_wit_2 : maxSlidingWindow_partial_solve_wit_2
  proof_of_maxSlidingWindow_partial_solve_wit_3 : maxSlidingWindow_partial_solve_wit_3
  proof_of_maxSlidingWindow_partial_solve_wit_4 : maxSlidingWindow_partial_solve_wit_4
  proof_of_maxSlidingWindow_partial_solve_wit_5 : maxSlidingWindow_partial_solve_wit_5
  proof_of_maxSlidingWindow_partial_solve_wit_6 : maxSlidingWindow_partial_solve_wit_6
  proof_of_maxSlidingWindow_partial_solve_wit_7 : maxSlidingWindow_partial_solve_wit_7
  proof_of_maxSlidingWindow_partial_solve_wit_8 : maxSlidingWindow_partial_solve_wit_8
  proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1
  proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2
  proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3
  proof_of_maxSlidingWindow_entail_wit_4_1 : maxSlidingWindow_entail_wit_4_1
  proof_of_maxSlidingWindow_entail_wit_4_2 : maxSlidingWindow_entail_wit_4_2
  proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5
  proof_of_maxSlidingWindow_entail_wit_6 : maxSlidingWindow_entail_wit_6
  proof_of_maxSlidingWindow_entail_wit_7_1 : maxSlidingWindow_entail_wit_7_1
  proof_of_maxSlidingWindow_entail_wit_7_2 : maxSlidingWindow_entail_wit_7_2
  proof_of_maxSlidingWindow_entail_wit_8 : maxSlidingWindow_entail_wit_8
  proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9
  proof_of_maxSlidingWindow_entail_wit_10 : maxSlidingWindow_entail_wit_10
  proof_of_maxSlidingWindow_entail_wit_11_1 : maxSlidingWindow_entail_wit_11_1
  proof_of_maxSlidingWindow_entail_wit_11_2 : maxSlidingWindow_entail_wit_11_2
  proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12
  proof_of_maxSlidingWindow_entail_wit_13 : maxSlidingWindow_entail_wit_13

end SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_goal
