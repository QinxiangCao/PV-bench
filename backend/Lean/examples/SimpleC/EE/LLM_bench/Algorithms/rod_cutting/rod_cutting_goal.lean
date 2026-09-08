import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib
open SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance rod_cutting_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def rod_cutting_safety_wit_1 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_full revenue_pre (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rod_cutting_safety_wit_2 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_full revenue_pre (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rod_cutting_safety_wit_3 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) ,
  (((revenue_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg revenue_pre 1 (n_pre + 1))
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def rod_cutting_safety_wit_4 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l j)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rod_cutting_safety_wit_5 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l j)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def rod_cutting_safety_wit_6 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= (j - i))) (PreH2 : ((j - i) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1))) (PreH11 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1))) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= (j * 1000000))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j)) (PreH21 : (RodCutScanBest price_l revenue_l j i best)) (PreH22 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int)))) ”

noncomputable def rod_cutting_safety_wit_7 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= (j - i))) (PreH2 : ((j - i) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1))) (PreH11 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1))) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= (j * 1000000))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j)) (PreH21 : (RodCutScanBest price_l revenue_l j i best)) (PreH22 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ ((j - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - i)) ”

noncomputable def rod_cutting_safety_wit_8 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l j)) (PreH22 : (RodCutScanBest price_l revenue_l j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "best" ) )) # Int |-> (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int)))))
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def rod_cutting_safety_wit_9 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l j)) (PreH22 : (RodCutScanBest price_l revenue_l j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def rod_cutting_safety_wit_10 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l j)) (PreH15 : (RodCutScanBest price_l revenue_l j i best)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) (j + 1) (revenue_l ++ (best :: (@List.nil Int))))
  ** (intArray.undef_seg revenue_pre (j + 1) (n_pre + 1))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def rod_cutting_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) ,
  (((revenue_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg revenue_pre 1 (n_pre + 1))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (revenue_l)) = 1) ” &&
  “ (RodCutRevenueTable price_l revenue_l 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < 1)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) 1 revenue_l)
  ** (intArray.undef_seg revenue_pre 1 (n_pre + 1))
) \/
(
forall (n_pre : Int) (revenue_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (price_l)) = (n_pre + 1))) (PreH6 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) ,
  (((revenue_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (revenue_l)) = 1) ” &&
  “ (RodCutRevenueTable price_l revenue_l 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < 1)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.seg revenue_pre (0 : Int) 1 revenue_l)
)

noncomputable def rod_cutting_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j 1 (0 : Int)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  TT && emp 
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000)))) ” &&
  “ (RodCutScanBest price_l revenue_l_2 j 1 (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))

noncomputable def rod_cutting_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j 1 (0 : Int))

noncomputable def rod_cutting_entail_wit_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))

noncomputable def rod_cutting_entail_wit_3 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l j)) (PreH15 : (RodCutScanBest price_l revenue_l j i best)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ ((0 : Int) <= (j - i)) ” &&
  “ ((j - i) < j) ” &&
  “ (best <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (best >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i <= j) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j i best) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "revenue" ) )) # Ptr |-> (revenue_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))

noncomputable def rod_cutting_entail_wit_4_1 : Prop :=
  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((0 : Int) <= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ” &&
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))) <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_4_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))

noncomputable def rod_cutting_entail_wit_4_2 : Prop :=
  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j (i + 1) best) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1) best) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_4_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1) best)

noncomputable def rod_cutting_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) (j + 1) (revenue_l_2 ++ (best :: (@List.nil Int))))
  ** (intArray.undef_seg revenue_pre (j + 1) (n_pre + 1))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (revenue_l)) = (j + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l (j + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (j + 1))) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) (j + 1) revenue_l)
  ** (intArray.undef_seg revenue_pre (j + 1) (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  TT && emp 
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (j + 1))) -> (((0 : Int) <= (Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int))) ∧ ((Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int)) <= (k_2 * 1000000)))) ” &&
  “ (RodCutRevenueTable price_l (revenue_l_2 ++ (best :: (@List.nil Int))) (j + 1)) ” &&
  “ ((Zlength ((revenue_l_2 ++ (best :: (@List.nil Int))))) = (j + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (j + 1))) -> (((0 : Int) <= (Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int))) ∧ ((Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int)) <= (k_2 * 1000000))))

noncomputable def rod_cutting_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (RodCutRevenueTable price_l (revenue_l_2 ++ (best :: (@List.nil Int))) (j + 1))

noncomputable def rod_cutting_entail_wit_5_split_goal_3 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  ((Zlength ((revenue_l_2 ++ (best :: (@List.nil Int))))) = (j + 1))

noncomputable def rod_cutting_entail_wit_5_split_goal_4 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))

noncomputable def rod_cutting_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 price_l (0 : Int))) ∧ ((Znth k_2 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < j)) -> (((0 : Int) <= (Znth k_3 revenue_l_2 (0 : Int))) ∧ ((Znth k_3 revenue_l_2 (0 : Int)) <= (k_3 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ ((Zlength (revenue_l)) = (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l (n_pre + 1)) ” &&
  “ ((Znth (n_pre - (0 : Int)) revenue_l_2 (0 : Int)) = (Znth n_pre revenue_l (0 : Int))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre + 1))) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.full revenue_pre (n_pre + 1) revenue_l)
) \/
(
forall (n_pre : Int) (revenue_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 price_l (0 : Int))) ∧ ((Znth k_2 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < j)) -> (((0 : Int) <= (Znth k_3 revenue_l_2 (0 : Int))) ∧ ((Znth k_3 revenue_l_2 (0 : Int)) <= (k_3 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
|--
  EX revenue_l : (List Int),
  “ ((Zlength (revenue_l)) = (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l (n_pre + 1)) ” &&
  “ ((Znth (n_pre - (0 : Int)) revenue_l_2 (0 : Int)) = (Znth n_pre revenue_l (0 : Int))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre + 1))) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full revenue_pre (n_pre + 1) revenue_l)
)

noncomputable def rod_cutting_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_full revenue_pre (n_pre + 1))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ”
  &&  (((revenue_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg revenue_pre 1 (n_pre + 1))
  ** (intArray.full price_pre (n_pre + 1) price_l)

noncomputable def rod_cutting_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= (j - i))) (PreH2 : ((j - i) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1))) (PreH11 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1))) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= (j * 1000000))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j)) (PreH21 : (RodCutScanBest price_l revenue_l j i best)) (PreH22 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ ((0 : Int) <= (j - i)) ” &&
  “ ((j - i) < j) ” &&
  “ (best <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (best >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i <= j) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j i best) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (((price_pre + (i * sizeof(INT)))) # Int |-> ((Znth i price_l (0 : Int))))
  ** (intArray.missing_i price_pre i (0 : Int) (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))

noncomputable def rod_cutting_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= (j - i))) (PreH2 : ((j - i) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1))) (PreH11 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1))) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= (j * 1000000))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j)) (PreH21 : (RodCutScanBest price_l revenue_l j i best)) (PreH22 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ ((0 : Int) <= (j - i)) ” &&
  “ ((j - i) < j) ” &&
  “ (best <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (best >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i <= j) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j i best) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (((revenue_pre + ((j - i) * sizeof(INT)))) # Int |-> ((Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))))
  ** (intArray.missing_i revenue_pre (j - i) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))

noncomputable def rod_cutting_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l j)) (PreH15 : (RodCutScanBest price_l revenue_l j i best)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ (i > j) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j i best) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (((revenue_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg revenue_pre (j + 1) (n_pre + 1))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)

noncomputable def rod_cutting_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l j)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  “ (j > n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (((revenue_pre + (n_pre * sizeof(INT)))) # Int |-> ((Znth (n_pre - (0 : Int)) revenue_l (0 : Int))))
  ** (intArray.missing_i revenue_pre n_pre (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)


structure VC_Correct : Type where
  proof_of_rod_cutting_safety_wit_1 : rod_cutting_safety_wit_1
  proof_of_rod_cutting_safety_wit_2 : rod_cutting_safety_wit_2
  proof_of_rod_cutting_safety_wit_3 : rod_cutting_safety_wit_3
  proof_of_rod_cutting_safety_wit_4 : rod_cutting_safety_wit_4
  proof_of_rod_cutting_safety_wit_5 : rod_cutting_safety_wit_5
  proof_of_rod_cutting_safety_wit_6 : rod_cutting_safety_wit_6
  proof_of_rod_cutting_safety_wit_7 : rod_cutting_safety_wit_7
  proof_of_rod_cutting_safety_wit_8 : rod_cutting_safety_wit_8
  proof_of_rod_cutting_safety_wit_9 : rod_cutting_safety_wit_9
  proof_of_rod_cutting_safety_wit_10 : rod_cutting_safety_wit_10
  proof_of_rod_cutting_entail_wit_3 : rod_cutting_entail_wit_3
  proof_of_rod_cutting_partial_solve_wit_1 : rod_cutting_partial_solve_wit_1
  proof_of_rod_cutting_partial_solve_wit_2 : rod_cutting_partial_solve_wit_2
  proof_of_rod_cutting_partial_solve_wit_3 : rod_cutting_partial_solve_wit_3
  proof_of_rod_cutting_partial_solve_wit_4 : rod_cutting_partial_solve_wit_4
  proof_of_rod_cutting_partial_solve_wit_5 : rod_cutting_partial_solve_wit_5
  proof_of_rod_cutting_entail_wit_1 : rod_cutting_entail_wit_1
  proof_of_rod_cutting_entail_wit_2 : rod_cutting_entail_wit_2
  proof_of_rod_cutting_entail_wit_4_1 : rod_cutting_entail_wit_4_1
  proof_of_rod_cutting_entail_wit_4_2 : rod_cutting_entail_wit_4_2
  proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5
  proof_of_rod_cutting_return_wit_1 : rod_cutting_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_goal
