import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib
open SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance huffman_encoding_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def huffman_cost_safety_wit_1 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (HuffmanInputBounded weights_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_full work_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_2 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied ++ remaining))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  (intArray.seg work_pre (0 : Int) (i + 1) (copied ++ ((Znth i weights_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg work_pre (i + 1) n_pre)
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_3 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied ++ remaining))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  ((( &( "total" ) )) # Int |->_)
  ** ((( &( "active" ) )) # Int |-> (n_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) i copied)
  ** (intArray.undef_seg work_pre i n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_4 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (1 <= active)) (PreH7 : (active <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= 56000)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH11 : (HuffmanProgress weights_l work_l active total)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def huffman_cost_safety_wit_5 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total)) ,
  ((( &( "first" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_6 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "first" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def huffman_cost_safety_wit_7 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) < (Znth first work_l (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l active total)) (PreH22 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre work_l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_8 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) >= (Znth first work_l (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l active total)) (PreH22 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre work_l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_9 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total)) (PreH19 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre work_l)
  ** ((( &( "x" ) )) # Int |-> ((Znth first work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((active - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (active - 1)) ”

noncomputable def huffman_cost_safety_wit_10 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l : (List Int)) (active : Int) (first : Int) (x : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l active x total)) ,
  ((( &( "second" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_11 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l : (List Int)) (active : Int) (first : Int) (x : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l active x total)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "second" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def huffman_cost_safety_wit_12 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) < (Znth second work_l (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH24 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre work_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_13 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) >= (Znth second work_l (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH24 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre work_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_14 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < n_pre)) (PreH14 : ((0 : Int) <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH23 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre work_l)
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((active - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (active - 1)) ”

noncomputable def huffman_cost_safety_wit_15 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total)) ,
  ((( &( "merged" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ ((x + y) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + y)) ”

noncomputable def huffman_cost_safety_wit_16 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total)) ,
  ((( &( "merged" ) )) # Int |-> ((x + y)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ ((total + (x + y)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total + (x + y))) ”

noncomputable def huffman_cost_safety_wit_17 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total)) ,
  (intArray.full work_pre n_pre (replace_Znth (active) ((x + y)) (work_l)))
  ** ((( &( "merged" ) )) # Int |-> ((x + y)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "work" ) )) # Ptr |-> (work_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "total" ) )) # Int |-> ((total + (x + y))))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((active + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (active + 1)) ”

noncomputable def huffman_cost_entail_wit_1 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (HuffmanInputBounded weights_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_full work_pre n_pre)
|--
  EX copied : (List Int), EX remaining : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) (0 : Int) copied)
  ** (intArray.undef_seg work_pre (0 : Int) n_pre)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (HuffmanInputBounded weights_l)) ,
  TT && emp 
|--
  EX remaining : (List Int),
  “ (weights_l = ((@List.nil Int) ++ remaining)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (weights_l))) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_2 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied_2 : (List Int)) (remaining_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied_2 ++ remaining_2))) (PreH7 : ((Zlength (copied_2)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  (intArray.seg work_pre (0 : Int) (i + 1) (copied_2 ++ ((Znth i weights_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg work_pre (i + 1) n_pre)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX copied : (List Int), EX remaining : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = (i + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) (i + 1) copied)
  ** (intArray.undef_seg work_pre (i + 1) n_pre)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (i : Int) (copied_2 : (List Int)) (remaining_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied_2 ++ remaining_2))) (PreH7 : ((Zlength (copied_2)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  TT && emp 
|--
  EX remaining : (List Int),
  “ ((copied_2 ++ remaining_2) = ((copied_2 ++ ((Znth (Zlength (copied_2)) (copied_2 ++ remaining_2) (0 : Int)) :: (@List.nil Int))) ++ remaining)) ” &&
  “ ((Zlength ((copied_2 ++ ((Znth (Zlength (copied_2)) (copied_2 ++ remaining_2) (0 : Int)) :: (@List.nil Int))))) = ((Zlength (copied_2)) + 1)) ” &&
  “ ((0 : Int) <= ((Zlength (copied_2)) + 1)) ” &&
  “ (((Zlength (copied_2)) + 1) <= (Zlength ((copied_2 ++ remaining_2)))) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_3 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied ++ remaining))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) i copied)
  ** (intArray.undef_seg work_pre i n_pre)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l n_pre (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (work_pre : Int) (n_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied ++ remaining))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  (intArray.seg work_pre (0 : Int) i copied)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l n_pre (0 : Int)) ”
  &&  (intArray.full work_pre n_pre work_l)
)

noncomputable def huffman_cost_entail_wit_4 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l_2)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= active) ” &&
  “ (1 <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 1) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l 1 (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 1 (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000))) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total)) ,
  (HuffmanMinScan work_l_2 1 (0 : Int))

noncomputable def huffman_cost_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))

noncomputable def huffman_cost_entail_wit_5 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total)) (PreH19 : (HuffmanMinScan work_l i first)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)

noncomputable def huffman_cost_entail_wit_6_1 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total)) (PreH22 : (HuffmanMinScan work_l_2 i first)) ,
  (intArray.full work_pre n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (i + 1)) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l (i + 1) i) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total)) (PreH22 : (HuffmanMinScan work_l_2 i first)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) i) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_6_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total)) (PreH22 : (HuffmanMinScan work_l_2 i first)) ,
  (HuffmanMinScan work_l_2 (i + 1) i)

noncomputable def huffman_cost_entail_wit_6_2 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total)) (PreH22 : (HuffmanMinScan work_l_2 i first)) ,
  (intArray.full work_pre n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < (i + 1)) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l (i + 1) first) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total)) (PreH22 : (HuffmanMinScan work_l_2 i first)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) first) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_6_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total)) (PreH22 : (HuffmanMinScan work_l_2 i first)) ,
  (HuffmanMinScan work_l_2 (i + 1) first)

noncomputable def huffman_cost_entail_wit_7 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total)) (PreH19 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_entail_wit_8 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX work_l_2 : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l_2)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ (1 <= (Znth first work_l (0 : Int))) ” &&
  “ ((Znth first work_l (0 : Int)) <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active - 1))) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l_2 (active - 1) (Znth first work_l (0 : Int)) total) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l_2)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  TT && emp 
|--
  “ (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)) (active - 1) (Znth first work_l (0 : Int)) total) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active - 1))) -> ((1 <= (Znth (k) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int)))) ∧ ((Znth (k) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int))) <= 8000))) ” &&
  “ ((Znth first work_l (0 : Int)) <= 8000) ” &&
  “ (1 <= (Znth first work_l (0 : Int))) ” &&
  “ ((Zlength ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))) = n_pre) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)) (active - 1) (Znth first work_l (0 : Int)) total)

noncomputable def huffman_cost_entail_wit_8_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active - 1))) -> ((1 <= (Znth (k) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int)))) ∧ ((Znth (k) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int))) <= 8000)))

noncomputable def huffman_cost_entail_wit_8_split_goal_3 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  ((Znth first work_l (0 : Int)) <= 8000)

noncomputable def huffman_cost_entail_wit_8_split_goal_4 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (1 <= (Znth first work_l (0 : Int)))

noncomputable def huffman_cost_entail_wit_8_split_goal_5 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  ((Zlength ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))) = n_pre)

noncomputable def huffman_cost_entail_wit_9 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (x : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l_2)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= active) ” &&
  “ (1 < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 1) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l 1 (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (x : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 1 (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000))) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (x : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total)) ,
  (HuffmanMinScan work_l_2 1 (0 : Int))

noncomputable def huffman_cost_entail_wit_9_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (x : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))

noncomputable def huffman_cost_entail_wit_10_1 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH24 : (HuffmanMinScan work_l_2 i second)) ,
  (intArray.full work_pre n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (i + 1)) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l (i + 1) i) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH24 : (HuffmanMinScan work_l_2 i second)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) i) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_10_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH24 : (HuffmanMinScan work_l_2 i second)) ,
  (HuffmanMinScan work_l_2 (i + 1) i)

noncomputable def huffman_cost_entail_wit_10_2 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH24 : (HuffmanMinScan work_l_2 i second)) ,
  (intArray.full work_pre n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < (i + 1)) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l (i + 1) second) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH24 : (HuffmanMinScan work_l_2 i second)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) second) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_10_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH24 : (HuffmanMinScan work_l_2 i second)) ,
  (HuffmanMinScan work_l_2 (i + 1) second)

noncomputable def huffman_cost_entail_wit_11 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < n_pre)) (PreH14 : ((0 : Int) <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH23 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_entail_wit_12 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX work_l_2 : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l_2)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ ((0 : Int) <= (active - 1)) ” &&
  “ ((active - 1) <= (n_pre - 2)) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ (1 <= (Znth second work_l (0 : Int))) ” &&
  “ ((Znth second work_l (0 : Int)) <= 8000) ” &&
  “ ((x + (Znth second work_l (0 : Int))) <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (((total + x) + (Znth second work_l (0 : Int))) <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active - 1))) -> ((1 <= (Znth (k) (work_l_2) ((0 : Int)))) ∧ ((Znth (k) (work_l_2) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanPairReady weights_l work_l_2 (active - 1) x (Znth second work_l (0 : Int)) total) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l_2)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  TT && emp 
|--
  “ (HuffmanPairReady weights_l (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)) (active - 1) x (Znth second work_l (0 : Int)) total) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active - 1))) -> ((1 <= (Znth (k) ((replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int)))) ∧ ((Znth (k) ((replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int))) <= 8000))) ” &&
  “ (((total + x) + (Znth second work_l (0 : Int))) <= 56000) ” &&
  “ ((x + (Znth second work_l (0 : Int))) <= 8000) ” &&
  “ ((Znth second work_l (0 : Int)) <= 8000) ” &&
  “ (1 <= (Znth second work_l (0 : Int))) ” &&
  “ ((Zlength ((replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))) = n_pre) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_12_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (HuffmanPairReady weights_l (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)) (active - 1) x (Znth second work_l (0 : Int)) total)

noncomputable def huffman_cost_entail_wit_12_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active - 1))) -> ((1 <= (Znth (k) ((replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int)))) ∧ ((Znth (k) ((replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l))) ((0 : Int))) <= 8000)))

noncomputable def huffman_cost_entail_wit_12_split_goal_3 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (((total + x) + (Znth second work_l (0 : Int))) <= 56000)

noncomputable def huffman_cost_entail_wit_12_split_goal_4 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((x + (Znth second work_l (0 : Int))) <= 8000)

noncomputable def huffman_cost_entail_wit_12_split_goal_5 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((Znth second work_l (0 : Int)) <= 8000)

noncomputable def huffman_cost_entail_wit_12_split_goal_6 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (1 <= (Znth second work_l (0 : Int)))

noncomputable def huffman_cost_entail_wit_12_split_goal_7 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) ((0 : Int)))) ∧ ((Znth (k_2) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((Zlength ((replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))) = n_pre)

noncomputable def huffman_cost_entail_wit_13 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total)) ,
  (intArray.full work_pre n_pre (replace_Znth (active) ((x + y)) (work_l_2)))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= (active + 1)) ” &&
  “ ((active + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (total + (x + y))) ” &&
  “ ((total + (x + y)) <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active + 1))) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l (active + 1) (total + (x + y))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total)) ,
  TT && emp 
|--
  “ (HuffmanProgress weights_l (replace_Znth (active) ((x + y)) (work_l_2)) (active + 1) (total + (x + y))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active + 1))) -> ((1 <= (Znth (k) ((replace_Znth (active) ((x + y)) (work_l_2))) ((0 : Int)))) ∧ ((Znth (k) ((replace_Znth (active) ((x + y)) (work_l_2))) ((0 : Int))) <= 8000))) ” &&
  “ ((Zlength ((replace_Znth (active) ((x + y)) (work_l_2)))) = n_pre) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_13_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total)) ,
  (HuffmanProgress weights_l (replace_Znth (active) ((x + y)) (work_l_2)) (active + 1) (total + (x + y)))

noncomputable def huffman_cost_entail_wit_13_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (active + 1))) -> ((1 <= (Znth (k) ((replace_Znth (active) ((x + y)) (work_l_2))) ((0 : Int)))) ∧ ((Znth (k) ((replace_Znth (active) ((x + y)) (work_l_2))) ((0 : Int))) <= 8000)))

noncomputable def huffman_cost_entail_wit_13_split_goal_3 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (work_l_2 : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) ((0 : Int)))) ∧ ((Znth (k_2) (work_l_2) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total)) ,
  ((Zlength ((replace_Znth (active) ((x + y)) (work_l_2)))) = n_pre)

noncomputable def huffman_cost_entail_wit_14 : Prop :=
  (
forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  EX final_work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (final_work_l)) = n_pre) ” &&
  “ (active = 1) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (HuffmanOptimalCost weights_l total) ” &&
  “ (HuffmanScratchFinal weights_l final_work_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre final_work_l)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total)) ,
  TT && emp 
|--
  “ (HuffmanScratchFinal weights_l work_l) ” &&
  “ (HuffmanOptimalCost weights_l total) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_14_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total)) ,
  (HuffmanScratchFinal weights_l work_l)

noncomputable def huffman_cost_entail_wit_14_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total)) ,
  (HuffmanOptimalCost weights_l total)

noncomputable def huffman_cost_return_wit_1 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (final_work_l : (List Int)) (active : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (final_work_l)) = n_pre)) (PreH5 : (active = 1)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 56000)) (PreH8 : (HuffmanOptimalCost weights_l total)) (PreH9 : (HuffmanScratchFinal weights_l final_work_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre final_work_l)
|--
  EX work_l : (List Int),
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanOptimalCost weights_l total) ” &&
  “ (HuffmanScratchFinal weights_l work_l) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)

noncomputable def huffman_cost_partial_solve_wit_1 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied ++ remaining))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) i copied)
  ** (intArray.undef_seg work_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ”
  &&  (((weights_pre + (i * sizeof(INT)))) # Int |-> ((Znth i weights_l (0 : Int))))
  ** (intArray.missing_i weights_pre i (0 : Int) n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) i copied)
  ** (intArray.undef_seg work_pre i n_pre)

noncomputable def huffman_cost_partial_solve_wit_2 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : (weights_l = (copied ++ remaining))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) i copied)
  ** (intArray.undef_seg work_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ”
  &&  (((work_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg work_pre (i + 1) n_pre)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg work_pre (0 : Int) i copied)

noncomputable def huffman_cost_partial_solve_wit_3 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((work_pre + (i * sizeof(INT)))) # Int |-> ((Znth i work_l (0 : Int))))
  ** (intArray.missing_i work_pre i (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_4 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((work_pre + (first * sizeof(INT)))) # Int |-> ((Znth first work_l (0 : Int))))
  ** (intArray.missing_i work_pre first (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_5 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total)) (PreH19 : (HuffmanMinScan work_l i first)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((work_pre + (first * sizeof(INT)))) # Int |-> ((Znth first work_l (0 : Int))))
  ** (intArray.missing_i work_pre first (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_6 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((work_pre + ((active - 1) * sizeof(INT)))) # Int |-> ((Znth (active - 1) work_l (0 : Int))))
  ** (intArray.missing_i work_pre (active - 1) (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_7 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((work_pre + (first * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i work_pre first (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_8 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < n_pre)) (PreH14 : ((0 : Int) <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH23 : (HuffmanMinScan work_l i second)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((work_pre + (i * sizeof(INT)))) # Int |-> ((Znth i work_l (0 : Int))))
  ** (intArray.missing_i work_pre i (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_9 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < n_pre)) (PreH14 : ((0 : Int) <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH23 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((work_pre + (second * sizeof(INT)))) # Int |-> ((Znth second work_l (0 : Int))))
  ** (intArray.missing_i work_pre second (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_10 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= first)) (PreH13 : (first < n_pre)) (PreH14 : ((0 : Int) <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH23 : (HuffmanMinScan work_l i second)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((work_pre + (second * sizeof(INT)))) # Int |-> ((Znth second work_l (0 : Int))))
  ** (intArray.missing_i work_pre second (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_11 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((work_pre + ((active - 1) * sizeof(INT)))) # Int |-> ((Znth (active - 1) work_l (0 : Int))))
  ** (intArray.missing_i work_pre (active - 1) (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_12 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= (active - 1))) (PreH2 : ((active - 1) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full work_pre n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((work_pre + (second * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i work_pre second (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_13 : Prop :=
  forall (work_pre : Int) (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (work_l : (List Int)) (active : Int) (first : Int) (second : Int) (x : Int) (y : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l)) (PreH6 : ((0 : Int) <= active)) (PreH7 : (active <= (n_pre - 2))) (PreH8 : ((0 : Int) <= first)) (PreH9 : (first < n_pre)) (PreH10 : ((0 : Int) <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y) <= 8000)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (((total + x) + y) <= 56000)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full work_pre n_pre work_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (HuffmanInputBounded weights_l) ” &&
  “ ((0 : Int) <= active) ” &&
  “ (active <= (n_pre - 2)) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ (1 <= y) ” &&
  “ (y <= 8000) ” &&
  “ ((x + y) <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (((total + x) + y) <= 56000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < active)) -> ((1 <= (Znth (k) (work_l) ((0 : Int)))) ∧ ((Znth (k) (work_l) ((0 : Int))) <= 8000))) ” &&
  “ (HuffmanPairReady weights_l work_l active x y total) ”
  &&  (((work_pre + (active * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i work_pre active (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)


structure VC_Correct : Type where
  proof_of_huffman_cost_safety_wit_1 : huffman_cost_safety_wit_1
  proof_of_huffman_cost_safety_wit_2 : huffman_cost_safety_wit_2
  proof_of_huffman_cost_safety_wit_3 : huffman_cost_safety_wit_3
  proof_of_huffman_cost_safety_wit_4 : huffman_cost_safety_wit_4
  proof_of_huffman_cost_safety_wit_5 : huffman_cost_safety_wit_5
  proof_of_huffman_cost_safety_wit_6 : huffman_cost_safety_wit_6
  proof_of_huffman_cost_safety_wit_7 : huffman_cost_safety_wit_7
  proof_of_huffman_cost_safety_wit_8 : huffman_cost_safety_wit_8
  proof_of_huffman_cost_safety_wit_9 : huffman_cost_safety_wit_9
  proof_of_huffman_cost_safety_wit_10 : huffman_cost_safety_wit_10
  proof_of_huffman_cost_safety_wit_11 : huffman_cost_safety_wit_11
  proof_of_huffman_cost_safety_wit_12 : huffman_cost_safety_wit_12
  proof_of_huffman_cost_safety_wit_13 : huffman_cost_safety_wit_13
  proof_of_huffman_cost_safety_wit_14 : huffman_cost_safety_wit_14
  proof_of_huffman_cost_safety_wit_15 : huffman_cost_safety_wit_15
  proof_of_huffman_cost_safety_wit_16 : huffman_cost_safety_wit_16
  proof_of_huffman_cost_safety_wit_17 : huffman_cost_safety_wit_17
  proof_of_huffman_cost_entail_wit_5 : huffman_cost_entail_wit_5
  proof_of_huffman_cost_entail_wit_7 : huffman_cost_entail_wit_7
  proof_of_huffman_cost_entail_wit_11 : huffman_cost_entail_wit_11
  proof_of_huffman_cost_return_wit_1 : huffman_cost_return_wit_1
  proof_of_huffman_cost_partial_solve_wit_1 : huffman_cost_partial_solve_wit_1
  proof_of_huffman_cost_partial_solve_wit_2 : huffman_cost_partial_solve_wit_2
  proof_of_huffman_cost_partial_solve_wit_3 : huffman_cost_partial_solve_wit_3
  proof_of_huffman_cost_partial_solve_wit_4 : huffman_cost_partial_solve_wit_4
  proof_of_huffman_cost_partial_solve_wit_5 : huffman_cost_partial_solve_wit_5
  proof_of_huffman_cost_partial_solve_wit_6 : huffman_cost_partial_solve_wit_6
  proof_of_huffman_cost_partial_solve_wit_7 : huffman_cost_partial_solve_wit_7
  proof_of_huffman_cost_partial_solve_wit_8 : huffman_cost_partial_solve_wit_8
  proof_of_huffman_cost_partial_solve_wit_9 : huffman_cost_partial_solve_wit_9
  proof_of_huffman_cost_partial_solve_wit_10 : huffman_cost_partial_solve_wit_10
  proof_of_huffman_cost_partial_solve_wit_11 : huffman_cost_partial_solve_wit_11
  proof_of_huffman_cost_partial_solve_wit_12 : huffman_cost_partial_solve_wit_12
  proof_of_huffman_cost_partial_solve_wit_13 : huffman_cost_partial_solve_wit_13
  proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1
  proof_of_huffman_cost_entail_wit_2 : huffman_cost_entail_wit_2
  proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3
  proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4
  proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1
  proof_of_huffman_cost_entail_wit_6_2 : huffman_cost_entail_wit_6_2
  proof_of_huffman_cost_entail_wit_8 : huffman_cost_entail_wit_8
  proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9
  proof_of_huffman_cost_entail_wit_10_1 : huffman_cost_entail_wit_10_1
  proof_of_huffman_cost_entail_wit_10_2 : huffman_cost_entail_wit_10_2
  proof_of_huffman_cost_entail_wit_12 : huffman_cost_entail_wit_12
  proof_of_huffman_cost_entail_wit_13 : huffman_cost_entail_wit_13
  proof_of_huffman_cost_entail_wit_14 : huffman_cost_entail_wit_14

end SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_goal
