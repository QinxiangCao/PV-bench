import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib
open SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance coin_change_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def coinChange_safety_wit_1 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_full dp_pre (amount_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_2 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_full dp_pre (amount_pre + 1))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def coinChange_safety_wit_3 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) 1 ((1 : Int) :: (@List.nil Int)))
  ** (intArray.undef_seg dp_pre 1 (amount_pre + 1))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def coinChange_safety_wit_4 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l j)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l)
  ** (intArray.undef_seg dp_pre j (amount_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_5 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l j)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.seg dp_pre (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (j + 1) (amount_pre + 1))
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def coinChange_safety_wit_6 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l (amount_pre + 1))) (PreH7 : (DpReachableTable (@List.nil Int) dp_l (amount_pre + 1))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_7 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1))) (PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
|--
  “ ((j - coin) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - coin)) ”

noncomputable def coinChange_safety_wit_8 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1))) (PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_9 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def coinChange_safety_wit_10 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) (replace_Znth (j) (1 : Int) (dp_l)))
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def coinChange_safety_wit_11 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def coinChange_safety_wit_12 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (i : Int) (coin : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < coinsSize_pre)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= INT_MAX)) (PreH11 : (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l (amount_pre + 1))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def coinChange_safety_wit_13 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (res : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : ((0 : Int) <= res)) (PreH7 : (res <= amount_pre)) (PreH8 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH9 : (NoReachableAbove coins_l amount_pre res)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_14 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (res : Int) (PreH1 : (res > (0 : Int))) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH10 : (NoReachableAbove coins_l amount_pre res)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_15 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH11 : (NoReachableAbove coins_l amount_pre res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((res - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (res - 1)) ”

noncomputable def coinChange_entail_wit_1 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (((dp_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
  ** (intArray.undef_seg dp_pre 1 (amount_pre + 1))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) 1 ((1 : Int) :: (@List.nil Int)))
  ** (intArray.undef_seg dp_pre 1 (amount_pre + 1))
) \/
(
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (((dp_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.seg dp_pre (0 : Int) 1 ((1 : Int) :: (@List.nil Int)))
)

noncomputable def coinChange_entail_wit_1_split_goal_1 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (((dp_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”

noncomputable def coinChange_entail_wit_1_split_goal_spatial : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (((dp_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
|--
  (intArray.seg dp_pre (0 : Int) 1 ((1 : Int) :: (@List.nil Int)))

noncomputable def coinChange_entail_wit_2 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) 1 ((1 : Int) :: (@List.nil Int)))
  ** (intArray.undef_seg dp_pre 1 (amount_pre + 1))
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (amount_pre + 1)) ” &&
  “ (DpPrefixZeroed dp_l 1) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) 1 dp_l)
  ** (intArray.undef_seg dp_pre 1 (amount_pre + 1))
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ” &&
  “ (DpPrefixZeroed (1 :: (@List.nil Int)) 1) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_2_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_2_split_goal_2 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpPrefixZeroed (1 :: (@List.nil Int)) 1)

noncomputable def coinChange_entail_wit_3 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l_2 j)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.seg dp_pre (0 : Int) (j + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (j + 1) (amount_pre + 1))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (amount_pre + 1)) ” &&
  “ (DpPrefixZeroed dp_l (j + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) (j + 1) dp_l)
  ** (intArray.undef_seg dp_pre (j + 1) (amount_pre + 1))
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l_2 j)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpPrefixZeroed (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_3_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l_2 j)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpPrefixZeroed (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1))

noncomputable def coinChange_entail_wit_4 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l_2 j)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l_2)
  ** (intArray.undef_seg dp_pre j (amount_pre + 1))
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ (DpPrefixZeroed dp_l (amount_pre + 1)) ” &&
  “ (DpReachableTable (@List.nil Int) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l_2 j)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.seg dp_pre (0 : Int) j dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ (DpPrefixZeroed dp_l (amount_pre + 1)) ” &&
  “ (DpReachableTable (@List.nil Int) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full dp_pre (amount_pre + 1) dp_l)
)

noncomputable def coinChange_entail_wit_5 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l_2 (amount_pre + 1))) (PreH7 : (DpReachableTable (@List.nil Int) dp_l_2 (amount_pre + 1))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((0 : Int)) (coins_l)) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l_2 (amount_pre + 1))) (PreH7 : (DpReachableTable (@List.nil Int) dp_l_2 (amount_pre + 1))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((0 : Int)) (coins_l)) dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_5_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l_2 (amount_pre + 1))) (PreH7 : (DpReachableTable (@List.nil Int) dp_l_2 (amount_pre + 1))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_5_split_goal_2 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l_2 (amount_pre + 1))) (PreH7 : (DpReachableTable (@List.nil Int) dp_l_2 (amount_pre + 1))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpReachableTable (sublist ((0 : Int)) ((0 : Int)) (coins_l)) dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_6 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ ((Znth i coins_l (0 : Int)) = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= (Znth i coins_l (0 : Int))) ” &&
  “ ((Znth i coins_l (0 : Int)) <= INT_MAX) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_6_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_7 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= coin) ” &&
  “ (coin <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l coin amount_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 coin amount_pre) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_7_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_7_split_goal_2 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 coin amount_pre)

noncomputable def coinChange_entail_wit_8_1 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) (replace_Znth (j) (1 : Int) (dp_l_2)))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= (j + 1)) ” &&
  “ ((j + 1) <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l (j + 1) amount_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1) amount_pre) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_8_1_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1) amount_pre)

noncomputable def coinChange_entail_wit_8_2 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l_2)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= (j + 1)) ” &&
  “ ((j + 1) <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l (j + 1) amount_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 (j + 1) amount_pre) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_8_2_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 (j + 1) amount_pre)

noncomputable def coinChange_entail_wit_9_1 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1))) (PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= INT_MAX) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1))) (PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_9_1_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1))) (PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_9_1_split_goal_2 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1))) (PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_9_2 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= INT_MAX) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_9_2_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_9_2_split_goal_2 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : (coin > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_10 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < coinsSize_pre)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= INT_MAX)) (PreH11 : (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= coinsSize_pre) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < coinsSize_pre)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= INT_MAX)) (PreH11 : (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_10_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (coin : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < coinsSize_pre)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= INT_MAX)) (PreH11 : (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_11 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre amount_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ” &&
  “ (NoReachableAbove coins_l amount_pre amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_11_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))

noncomputable def coinChange_entail_wit_11_split_goal_2 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (NoReachableAbove coins_l amount_pre amount_pre)

noncomputable def coinChange_entail_wit_11_split_goal_3 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l (0 : Int))) ∧ ((Znth k_2 coins_l (0 : Int)) <= INT_MAX)))) ,
  (DpReachableTable coins_l dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_12 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH11 : (NoReachableAbove coins_l amount_pre res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l_2)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= (res - 1)) ” &&
  “ ((res - 1) <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre (res - 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH11 : (NoReachableAbove coins_l amount_pre res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (NoReachableAbove coins_l amount_pre (res - 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_12_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH11 : (NoReachableAbove coins_l amount_pre res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (NoReachableAbove coins_l amount_pre (res - 1))

noncomputable def coinChange_entail_wit_13_1 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : (res <= (0 : Int))) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH10 : (NoReachableAbove coins_l amount_pre res)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre res) ” &&
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : (res <= (0 : Int))) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH10 : (NoReachableAbove coins_l amount_pre res)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_13_1_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : (res <= (0 : Int))) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH10 : (NoReachableAbove coins_l amount_pre res)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (MaxReachableAmount coins_l amount_pre res)

noncomputable def coinChange_entail_wit_13_2 : Prop :=
  (
forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH11 : (NoReachableAbove coins_l amount_pre res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l_2)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre res) ” &&
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
) \/
(
forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH11 : (NoReachableAbove coins_l amount_pre res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_13_2_split_goal_1 : Prop :=
  forall (amount_pre : Int) (coinsSize_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH11 : (NoReachableAbove coins_l amount_pre res)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (MaxReachableAmount coins_l amount_pre res)

noncomputable def coinChange_return_wit_1 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : ((0 : Int) <= res)) (PreH7 : (res <= amount_pre)) (PreH8 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH9 : (NoReachableAbove coins_l amount_pre res)) (PreH10 : (MaxReachableAmount coins_l amount_pre res)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l_2)
|--
  EX dp_l : (List Int),
  “ (MaxReachableAmount coins_l amount_pre res) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)

noncomputable def coinChange_partial_solve_wit_1 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_full dp_pre (amount_pre + 1))
|--
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (((dp_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre 1 (amount_pre + 1))
  ** (intArray.full coins_pre coinsSize_pre coins_l)

noncomputable def coinChange_partial_solve_wit_2 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1))) (PreH9 : (DpPrefixZeroed dp_l j)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l)
  ** (intArray.undef_seg dp_pre j (amount_pre + 1))
|--
  “ (j <= amount_pre) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (amount_pre + 1)) ” &&
  “ (DpPrefixZeroed dp_l j) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (j + 1) (amount_pre + 1))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l)

noncomputable def coinChange_partial_solve_wit_3 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (i : Int) (PreH1 : (i < coinsSize_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l (amount_pre + 1))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
|--
  “ (i < coinsSize_pre) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= coinsSize_pre) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l (amount_pre + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (((coins_pre + (i * sizeof(INT)))) # Int |-> ((Znth i coins_l (0 : Int))))
  ** (intArray.missing_i coins_pre i (0 : Int) coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)

noncomputable def coinChange_partial_solve_wit_4 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l (0 : Int)))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1))) (PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
|--
  “ (j <= amount_pre) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= j) ” &&
  “ (j <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (((dp_pre + ((j - coin) * sizeof(INT)))) # Int |-> ((Znth (j - coin) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre (j - coin) (0 : Int) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)

noncomputable def coinChange_partial_solve_wit_5 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l (0 : Int)))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1))) (PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full dp_pre (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int)) ” &&
  “ (j <= amount_pre) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= j) ” &&
  “ (j <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i dp_pre j (0 : Int) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)

noncomputable def coinChange_partial_solve_wit_6 : Prop :=
  forall (dp_pre : Int) (amount_pre : Int) (coinsSize_pre : Int) (coins_pre : Int) (coins_l : (List Int)) (dp_l : (List Int)) (res : Int) (PreH1 : (res > (0 : Int))) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : ((0 : Int) <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH10 : (NoReachableAbove coins_l amount_pre res)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX)))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full dp_pre (amount_pre + 1) dp_l)
|--
  “ (res > (0 : Int)) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((Zlength (coins_l)) = coinsSize_pre) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre res) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l (0 : Int))) ∧ ((Znth k coins_l (0 : Int)) <= INT_MAX))) ”
  &&  (((dp_pre + (res * sizeof(INT)))) # Int |-> ((Znth res dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre res (0 : Int) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)


structure VC_Correct : Type where
  proof_of_coinChange_safety_wit_1 : coinChange_safety_wit_1
  proof_of_coinChange_safety_wit_2 : coinChange_safety_wit_2
  proof_of_coinChange_safety_wit_3 : coinChange_safety_wit_3
  proof_of_coinChange_safety_wit_4 : coinChange_safety_wit_4
  proof_of_coinChange_safety_wit_5 : coinChange_safety_wit_5
  proof_of_coinChange_safety_wit_6 : coinChange_safety_wit_6
  proof_of_coinChange_safety_wit_7 : coinChange_safety_wit_7
  proof_of_coinChange_safety_wit_8 : coinChange_safety_wit_8
  proof_of_coinChange_safety_wit_9 : coinChange_safety_wit_9
  proof_of_coinChange_safety_wit_10 : coinChange_safety_wit_10
  proof_of_coinChange_safety_wit_11 : coinChange_safety_wit_11
  proof_of_coinChange_safety_wit_12 : coinChange_safety_wit_12
  proof_of_coinChange_safety_wit_13 : coinChange_safety_wit_13
  proof_of_coinChange_safety_wit_14 : coinChange_safety_wit_14
  proof_of_coinChange_safety_wit_15 : coinChange_safety_wit_15
  proof_of_coinChange_return_wit_1 : coinChange_return_wit_1
  proof_of_coinChange_partial_solve_wit_1 : coinChange_partial_solve_wit_1
  proof_of_coinChange_partial_solve_wit_2 : coinChange_partial_solve_wit_2
  proof_of_coinChange_partial_solve_wit_3 : coinChange_partial_solve_wit_3
  proof_of_coinChange_partial_solve_wit_4 : coinChange_partial_solve_wit_4
  proof_of_coinChange_partial_solve_wit_5 : coinChange_partial_solve_wit_5
  proof_of_coinChange_partial_solve_wit_6 : coinChange_partial_solve_wit_6
  proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1
  proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2
  proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3
  proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4
  proof_of_coinChange_entail_wit_5 : coinChange_entail_wit_5
  proof_of_coinChange_entail_wit_6 : coinChange_entail_wit_6
  proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7
  proof_of_coinChange_entail_wit_8_1 : coinChange_entail_wit_8_1
  proof_of_coinChange_entail_wit_8_2 : coinChange_entail_wit_8_2
  proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1
  proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2
  proof_of_coinChange_entail_wit_10 : coinChange_entail_wit_10
  proof_of_coinChange_entail_wit_11 : coinChange_entail_wit_11
  proof_of_coinChange_entail_wit_12 : coinChange_entail_wit_12
  proof_of_coinChange_entail_wit_13_1 : coinChange_entail_wit_13_1
  proof_of_coinChange_entail_wit_13_2 : coinChange_entail_wit_13_2

end SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_goal
