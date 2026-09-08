import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib
open SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance merging_stones_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def mergingStones_safety_wit_1 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre)) (PreH5 : (StoneTableShape dp_init n_pre)) ,
  ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_2 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre)) (PreH5 : (StoneTableShape dp_init n_pre)) ,
  ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_3 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre)) (PreH5 : (StoneTableShape dp_init n_pre)) (PreH6 : (StonePrefixProgress stones_l ((0 : Int) :: (@List.nil Int)) n_pre (0 : Int))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) 1 ((0 : Int) :: (@List.nil Int)))
  ** (intArray.undef_seg prefix_pre 1 (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_4 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def mergingStones_safety_wit_5 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_6 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int)))) ”
) \/
(
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int)))) ”
)

noncomputable def mergingStones_safety_wit_6_split_goal_1 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) <= INT_MAX) ”

noncomputable def mergingStones_safety_wit_6_split_goal_2 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int)))) ”

noncomputable def mergingStones_safety_wit_7 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.seg prefix_pre (0 : Int) ((i + 1) + 1) (prefix_l ++ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg prefix_pre ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def mergingStones_safety_wit_8 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) ,
  ((( &( "row" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_9 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (row : Int) (prefix_l : (List Int)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH10 : (StoneZeroRows dp_l n_pre row)) ,
  ((( &( "col" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_10 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (col : Int) (row : Int) (prefix_l : (List Int)) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneZeroProgress dp_l n_pre row col)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** ((( &( "col" ) )) # Int |-> (col))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((row * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (row * n_pre)) ”

noncomputable def mergingStones_safety_wit_11 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (col : Int) (row : Int) (prefix_l : (List Int)) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneZeroProgress dp_l n_pre row col)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** ((( &( "col" ) )) # Int |-> (col))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_12 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (col : Int) (row : Int) (prefix_l : (List Int)) (__default__List_Z : _List_Z) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneZeroProgress dp_l n_pre row col)) ,
  (((dp_pre + (((row * n_pre) + col) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.missing_i (dp_pre + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre row (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** ((( &( "col" ) )) # Int |-> (col))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
|--
  “ ((col + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (col + 1)) ”

noncomputable def mergingStones_safety_wit_13 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (row : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= row)) (PreH4 : (row < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH9 : (StoneZeroRows dp_l n_pre (row + 1))) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((row + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (row + 1)) ”

noncomputable def mergingStones_safety_wit_14 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (StoneZeroRows dp_l n_pre n_pre)) (PreH8 : (StoneLenDone stones_l dp_l n_pre 2)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def mergingStones_safety_wit_15 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (len : Int) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_16 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left <= ((n_pre - len) + 1))) (PreH7 : ((Zlength (stones_l)) = n_pre)) (PreH8 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH9 : (StoneMassesBounded stones_l n_pre)) (PreH10 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH11 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((left + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + len)) ”

noncomputable def mergingStones_safety_wit_17 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (((left + len) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + len) - 1)) ”

noncomputable def mergingStones_safety_wit_18 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((left + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + len)) ”

noncomputable def mergingStones_safety_wit_19 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_20 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ”
) \/
(
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ”
)

noncomputable def mergingStones_safety_wit_20_split_goal_1 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= INT_MAX) ”

noncomputable def mergingStones_safety_wit_20_split_goal_2 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((INT_MIN) <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ”

noncomputable def mergingStones_safety_wit_21 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((((left + len) - 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((left + len) - 1) + 1)) ”

noncomputable def mergingStones_safety_wit_22 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_23 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "best" ) )) # Int |->_)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |-> (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))))
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1000000 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000) ”

noncomputable def mergingStones_safety_wit_24 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH12 : (2 <= interval_sum)) (PreH13 : (interval_sum <= 8000)) (PreH14 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH15 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH16 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH17 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH18 : (StoneMassesBounded stones_l n_pre)) (PreH19 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((left * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * n_pre)) ”

noncomputable def mergingStones_safety_wit_25 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH17 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (((split + 1) * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((split + 1) * n_pre)) ”

noncomputable def mergingStones_safety_wit_26 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH17 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def mergingStones_safety_wit_27 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH17 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_28 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH17 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((dp_pre + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ”

noncomputable def mergingStones_safety_wit_29 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH17 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((dp_pre + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))))) ”

noncomputable def mergingStones_safety_wit_30 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (right_value = (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value) + interval_sum))) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l left right split candidate)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) best)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def mergingStones_safety_wit_31 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 56000)) (PreH15 : (StoneMassesBounded stones_l n_pre)) (PreH16 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH17 : (StoneSplitProgress stones_l dp_l n_pre len left right best)) (PreH18 : (StoneIntervalMin stones_l left right best)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((left * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * n_pre)) ”

noncomputable def mergingStones_safety_wit_32 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_old : (List (List Int))) (dp_new : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre)) (PreH14 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best)) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1))) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_new)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def mergingStones_safety_wit_33 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (StoneLenDone stones_l dp_l n_pre (len + 1))) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((len + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len + 1)) ”

noncomputable def mergingStones_safety_wit_34 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre)) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1))) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH7 : ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH8 : ((Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def mergingStones_safety_wit_35 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre)) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1))) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH7 : ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH8 : ((Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (((0 : Int) * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) * n_pre)) ”

noncomputable def mergingStones_safety_wit_36 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre)) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1))) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH7 : ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH8 : ((Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_37 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre)) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1))) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH7 : ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH8 : ((Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_entail_wit_1 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre)) (PreH5 : (StoneTableShape dp_init n_pre)) ,
  (((prefix_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg prefix_pre 1 (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l ((0 : Int) :: (@List.nil Int)) n_pre (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) 1 ((0 : Int) :: (@List.nil Int)))
  ** (intArray.undef_seg prefix_pre 1 (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
) \/
(
forall (prefix_pre : Int) (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) ,
  (((prefix_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
|--
  “ (StonePrefixProgress stones_l ((0 : Int) :: (@List.nil Int)) n_pre (0 : Int)) ”
  &&  (intArray.seg prefix_pre (0 : Int) 1 ((0 : Int) :: (@List.nil Int)))
)

noncomputable def mergingStones_entail_wit_1_split_goal_1 : Prop :=
  forall (prefix_pre : Int) (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) ,
  (((prefix_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
|--
  “ (StonePrefixProgress stones_l ((0 : Int) :: (@List.nil Int)) n_pre (0 : Int)) ”

noncomputable def mergingStones_entail_wit_1_split_goal_spatial : Prop :=
  forall (prefix_pre : Int) (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) ,
  (((prefix_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
|--
  (intArray.seg prefix_pre (0 : Int) 1 ((0 : Int) :: (@List.nil Int)))

noncomputable def mergingStones_entail_wit_2 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre)) (PreH5 : (StoneTableShape dp_init n_pre)) (PreH6 : (StonePrefixProgress stones_l ((0 : Int) :: (@List.nil Int)) n_pre (0 : Int))) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) 1 ((0 : Int) :: (@List.nil Int)))
  ** (intArray.undef_seg prefix_pre 1 (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l n_pre (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) ((0 : Int) + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre ((0 : Int) + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
) \/
(
forall (prefix_pre : Int) (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre)) (PreH5 : (StoneTableShape dp_init n_pre)) (PreH6 : (StonePrefixProgress stones_l ((0 : Int) :: (@List.nil Int)) n_pre (0 : Int))) ,
  (intArray.seg prefix_pre (0 : Int) 1 ((0 : Int) :: (@List.nil Int)))
|--
  EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l n_pre (0 : Int)) ”
  &&  (intArray.seg prefix_pre (0 : Int) ((0 : Int) + 1) prefix_l)
)

noncomputable def mergingStones_entail_wit_3 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l_2)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l n_pre i) ” &&
  “ ((0 : Int) <= (Znth i prefix_l (0 : Int))) ” &&
  “ ((Znth i prefix_l (0 : Int)) <= 8000) ” &&
  “ (1 <= (Znth i stones_l (0 : Int))) ” &&
  “ ((Znth i stones_l (0 : Int)) <= 1000) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
) \/
(
forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  TT && emp 
|--
  “ ((Znth i stones_l (0 : Int)) <= 1000) ” &&
  “ (1 <= (Znth i stones_l (0 : Int))) ” &&
  “ ((Znth i prefix_l_2 (0 : Int)) <= 8000) ” &&
  “ ((0 : Int) <= (Znth i prefix_l_2 (0 : Int))) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  ((Znth i stones_l (0 : Int)) <= 1000)

noncomputable def mergingStones_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  (1 <= (Znth i stones_l (0 : Int)))

noncomputable def mergingStones_entail_wit_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  ((Znth i prefix_l_2 (0 : Int)) <= 8000)

noncomputable def mergingStones_entail_wit_3_split_goal_4 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  ((0 : Int) <= (Znth i prefix_l_2 (0 : Int)))

noncomputable def mergingStones_entail_wit_4 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l_2 (0 : Int)))) (PreH10 : ((Znth i prefix_l_2 (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.seg prefix_pre (0 : Int) ((i + 1) + 1) (prefix_l_2 ++ (((Znth (i - (0 : Int)) prefix_l_2 (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg prefix_pre ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l n_pre (i + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) ((i + 1) + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre ((i + 1) + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
) \/
(
forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l_2 (0 : Int)))) (PreH10 : ((Znth i prefix_l_2 (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  TT && emp 
|--
  “ (StonePrefixProgress stones_l (prefix_l_2 ++ (((Znth (i - (0 : Int)) prefix_l_2 (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))) n_pre (i + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l_2 (0 : Int)))) (PreH10 : ((Znth i prefix_l_2 (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (StonePrefixProgress stones_l (prefix_l_2 ++ (((Znth (i - (0 : Int)) prefix_l_2 (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))) n_pre (i + 1))

noncomputable def mergingStones_entail_wit_5 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l_2)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
) \/
(
forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  TT && emp 
|--
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ ((Zlength (prefix_l_2)) = (n_pre + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  (StonePrefixDone stones_l prefix_l_2 n_pre)

noncomputable def mergingStones_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StoneTableShape dp_init n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i)) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1))

noncomputable def mergingStones_entail_wit_6 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneZeroRows dp_l n_pre (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_init n_pre (0 : Int)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_6_split_goal_1 : Prop :=
  forall (n_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) ,
  (StoneZeroRows dp_init n_pre (0 : Int))

noncomputable def mergingStones_entail_wit_7 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneZeroRows dp_l_2 n_pre row)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneZeroProgress dp_l n_pre row (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneZeroRows dp_l_2 n_pre row)) ,
  TT && emp 
|--
  “ (StoneZeroProgress dp_l_2 n_pre row (0 : Int)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneZeroRows dp_l_2 n_pre row)) ,
  (StoneZeroProgress dp_l_2 n_pre row (0 : Int))

noncomputable def mergingStones_entail_wit_8 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (__default__List_Z : _List_Z) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col)) ,
  (((dp_pre + (((row * n_pre) + col) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.missing_i (dp_pre + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l_2 __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre row (0 : Int) n_pre n_pre dp_l_2)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= (col + 1)) ” &&
  “ ((col + 1) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneZeroProgress dp_l n_pre row (col + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (dp_pre : Int) (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (__default__List_Z : _List_Z) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : (col < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneMassesBounded stones_l n_pre)) (PreH13 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH14 : (StoneZeroProgress dp_l_2 n_pre row col)) ,
  (((dp_pre + (((row * n_pre) + col) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.missing_i (dp_pre + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l_2 __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre row (0 : Int) n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l_2)) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= (col + 1)) ” &&
  “ ((col + 1) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (StoneZeroProgress dp_l n_pre row (col + 1)) ”
  &&  (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
)

noncomputable def mergingStones_entail_wit_9 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneZeroRows dp_l n_pre (row + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col)) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_l_2 n_pre (row + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col)) ,
  (StoneZeroRows dp_l_2 n_pre (row + 1))

noncomputable def mergingStones_entail_wit_10 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= row)) (PreH4 : (row < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH7 : (StoneMassesBounded stones_l n_pre)) (PreH8 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH9 : (StoneZeroRows dp_l_2 n_pre (row + 1))) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= (row + 1)) ” &&
  “ ((row + 1) <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneZeroRows dp_l n_pre (row + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)

noncomputable def mergingStones_entail_wit_11 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneZeroRows dp_l_2 n_pre row)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneZeroRows dp_l n_pre n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre 2) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneZeroRows dp_l_2 n_pre row)) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre 2) ” &&
  “ (StoneZeroRows dp_l_2 n_pre n_pre) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_11_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneZeroRows dp_l_2 n_pre row)) ,
  (StoneLenDone stones_l dp_l_2 n_pre 2)

noncomputable def mergingStones_entail_wit_11_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (row : Int) (prefix_l_2 : (List Int)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneZeroRows dp_l_2 n_pre row)) ,
  (StoneZeroRows dp_l_2 n_pre n_pre)

noncomputable def mergingStones_entail_wit_12 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneZeroRows dp_l_2 n_pre n_pre)) (PreH8 : (StoneLenDone stones_l dp_l_2 n_pre 2)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre 2) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)

noncomputable def mergingStones_entail_wit_13 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - len) + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  TT && emp 
|--
  “ (StoneLeftProgress stones_l dp_l_2 n_pre len (0 : Int)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_13_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  (StoneLeftProgress stones_l dp_l_2 n_pre len (0 : Int))

noncomputable def mergingStones_entail_wit_14 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l_2 : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (((left + len) - 1) = ((left + len) - 1)) ” &&
  “ (left < ((left + len) - 1)) ” &&
  “ (((left + len) - 1) < n_pre) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) = (sum ((sublist (left) ((((left + len) - 1) + 1)) (stones_l))))) ” &&
  “ (2 <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= 8000) ” &&
  “ (1000000 = 1000000) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l_2)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left left 1000000) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= 8000) ” &&
  “ (2 <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) = (sum ((sublist (left) ((((left + len) - 1) + 1)) (stones_l))))) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_14_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000)

noncomputable def mergingStones_entail_wit_14_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= 8000)

noncomputable def mergingStones_entail_wit_14_split_goal_3 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (2 <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))))

noncomputable def mergingStones_entail_wit_14_split_goal_4 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) = (sum ((sublist (left) ((((left + len) - 1) + 1)) (stones_l)))))

noncomputable def mergingStones_entail_wit_15 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : (best = 1000000)) (PreH14 : ((Zlength (stones_l)) = n_pre)) (PreH15 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH16 : (StoneMassesBounded stones_l n_pre)) (PreH17 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH18 : (StoneSplitProgress stones_l dp_l_2 n_pre len left left best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < n_pre) ” &&
  “ (left <= left) ” &&
  “ (left <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left left best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)

noncomputable def mergingStones_entail_wit_16 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left split best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  TT && emp 
|--
  “ ((Znth ((left + len) - 1) (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth ((left + len) - 1) (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ ((Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_16_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  ((Znth ((left + len) - 1) (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)) <= 56000)

noncomputable def mergingStones_entail_wit_16_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  ((0 : Int) <= (Znth ((left + len) - 1) (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))

noncomputable def mergingStones_entail_wit_16_split_goal_3 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  ((Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)) <= 56000)

noncomputable def mergingStones_entail_wit_16_split_goal_4 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  ((0 : Int) <= (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))

noncomputable def mergingStones_entail_wit_17 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH12 : (2 <= interval_sum)) (PreH13 : (interval_sum <= 8000)) (PreH14 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH15 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH16 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH17 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH18 : (StoneMassesBounded stones_l n_pre)) (PreH19 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (((dp_pre + (((left * n_pre) + split) * sizeof(INT)))) # Int |-> ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + ((left * n_pre) * sizeof(INT))) split (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre left (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
|--
  EX prefix_l : (List Int), EX dp_l_2 : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ ((Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ ((Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
) \/
(
forall (dp_pre : Int) (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (2 <= len)) (PreH6 : (len <= n_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : ((left + len) <= n_pre)) (PreH9 : (right = ((left + len) - 1))) (PreH10 : (left <= split)) (PreH11 : (split < right)) (PreH12 : (right < n_pre)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH17 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH18 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH19 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (((dp_pre + (((left * n_pre) + split) * sizeof(INT)))) # Int |-> ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + ((left * n_pre) * sizeof(INT))) split (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre left (0 : Int) n_pre n_pre dp_l)
|--
  EX dp_l_2 : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ ((Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ ((Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best) ”
  &&  (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
)

noncomputable def mergingStones_entail_wit_18 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH17 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (((dp_pre + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
|--
  EX prefix_l : (List Int), EX dp_l_2 : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))) = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) = ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ” &&
  “ ((0 : Int) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ” &&
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) <= 56000) ” &&
  “ (StoneSplitCandidate stones_l dp_l_2 left right split ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
) \/
(
forall (dp_pre : Int) (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (2 <= len)) (PreH6 : (len <= n_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : ((left + len) <= n_pre)) (PreH9 : (right = ((left + len) - 1))) (PreH10 : (left <= split)) (PreH11 : (split < right)) (PreH12 : (right < n_pre)) (PreH13 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH20 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH21 : (StoneMassesBounded stones_l n_pre)) (PreH22 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH23 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (((dp_pre + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (split + 1) (0 : Int) n_pre n_pre dp_l)
|--
  EX dp_l_2 : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))) = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ ((0 : Int) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ” &&
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) <= 56000) ” &&
  “ (StoneSplitCandidate stones_l dp_l_2 left right split ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best) ”
  &&  (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
)

noncomputable def mergingStones_entail_wit_19_1 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value) + interval_sum))) (PreH16 : ((0 : Int) <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int))) ” &&
  “ (right_value = (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int))) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (candidate = ((left_value + right_value) + interval_sum)) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 56000) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 1000000) ” &&
  “ (StoneSplitCandidate stones_l dp_l left right split candidate) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) candidate) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value) + interval_sum))) (PreH16 : ((0 : Int) <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) ((left_value + right_value) + interval_sum)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_19_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value) + interval_sum))) (PreH16 : ((0 : Int) <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) ((left_value + right_value) + interval_sum))

noncomputable def mergingStones_entail_wit_19_2 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value) + interval_sum))) (PreH16 : ((0 : Int) <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int))) ” &&
  “ (right_value = (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int))) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (candidate = ((left_value + right_value) + interval_sum)) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 56000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitCandidate stones_l dp_l left right split candidate) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value) + interval_sum))) (PreH16 : ((0 : Int) <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best) ” &&
  “ ((0 : Int) <= best) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_19_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value) + interval_sum))) (PreH16 : ((0 : Int) <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best)

noncomputable def mergingStones_entail_wit_19_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value) + interval_sum))) (PreH16 : ((0 : Int) <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  ((0 : Int) <= best)

noncomputable def mergingStones_entail_wit_20 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH12 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value) + interval_sum))) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < n_pre) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH12 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value) + interval_sum))) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best)) ,
  TT && emp 
|--
  “ ((Zlength (prefix_l_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (interval_sum <= 8000) ” &&
  “ (2 <= interval_sum) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_20_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH12 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value) + interval_sum))) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best)) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1))

noncomputable def mergingStones_entail_wit_20_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH12 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value) + interval_sum))) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best)) ,
  ((Zlength (stones_l)) = n_pre)

noncomputable def mergingStones_entail_wit_20_split_goal_3 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH12 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value) + interval_sum))) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best)) ,
  (interval_sum <= 8000)

noncomputable def mergingStones_entail_wit_20_split_goal_4 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (interval_sum : Int) (candidate : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) (PreH12 : (right_value = (Znth right (Znth (split + 1) dp_l_2 __default__List_Z) (0 : Int)))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value) + interval_sum))) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate)) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1) best)) ,
  (2 <= interval_sum)

noncomputable def mergingStones_entail_wit_21 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < n_pre) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left right best) ” &&
  “ (StoneIntervalMin stones_l left right best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  TT && emp 
|--
  “ (StoneIntervalMin stones_l left ((left + len) - 1) best) ” &&
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left ((left + len) - 1) best) ” &&
  “ (best <= 56000) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_21_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (StoneIntervalMin stones_l left ((left + len) - 1) best)

noncomputable def mergingStones_entail_wit_21_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left ((left + len) - 1) best)

noncomputable def mergingStones_entail_wit_21_split_goal_3 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + len) <= n_pre)) (PreH8 : (right = ((left + len) - 1))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH20 : (StoneMassesBounded stones_l n_pre)) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (best <= 56000)

noncomputable def mergingStones_entail_wit_22 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 56000)) (PreH15 : (StoneMassesBounded stones_l n_pre)) (PreH16 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH17 : (StoneSplitProgress stones_l dp_l n_pre len left right best)) (PreH18 : (StoneIntervalMin stones_l left right best)) ,
  (((dp_pre + (((left * n_pre) + right) * sizeof(INT)))) # Int |-> (best))
  ** (intArray.missing_i (dp_pre + ((left * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre left (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
|--
  EX dp_old : (List (List Int)), EX dp_new : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneUpdatedCell stones_l dp_old dp_new left right best) ” &&
  “ (StoneLeftProgress stones_l dp_new n_pre len (left + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_new)
) \/
(
forall (dp_pre : Int) (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (best <= INT_MAX)) (PreH2 : (best >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (2 <= len)) (PreH6 : (len <= n_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : ((left + len) <= n_pre)) (PreH9 : (right = ((left + len) - 1))) (PreH10 : (left < right)) (PreH11 : (right < n_pre)) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 56000)) (PreH17 : (StoneMassesBounded stones_l n_pre)) (PreH18 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left right best)) (PreH20 : (StoneIntervalMin stones_l left right best)) ,
  (((dp_pre + (((left * n_pre) + right) * sizeof(INT)))) # Int |-> (best))
  ** (intArray.missing_i (dp_pre + ((left * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre left (0 : Int) n_pre n_pre dp_l)
|--
  EX dp_old : (List (List Int)), EX dp_new : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (StoneUpdatedCell stones_l dp_old dp_new left right best) ” &&
  “ (StoneLeftProgress stones_l dp_new n_pre len (left + 1)) ”
  &&  (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_new)
)

noncomputable def mergingStones_entail_wit_23 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_old : (List (List Int))) (dp_new : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre)) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best)) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1))) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_new)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= ((n_pre - len) + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len (left + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_old : (List (List Int))) (dp_new : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre)) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best)) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1))) ,
  TT && emp 
|--
  “ ((Zlength (prefix_l_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_23_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_old : (List (List Int))) (dp_new : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre)) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best)) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1))) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1))

noncomputable def mergingStones_entail_wit_23_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_old : (List (List Int))) (dp_new : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre)) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best)) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1))) ,
  ((Zlength (stones_l)) = n_pre)

noncomputable def mergingStones_entail_wit_24 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre (len + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre (len + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_24_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (StoneLenDone stones_l dp_l_2 n_pre (len + 1))

noncomputable def mergingStones_entail_wit_25 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1))) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= (len + 1)) ” &&
  “ ((len + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre (len + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1))) ,
  TT && emp 
|--
  “ ((Zlength (prefix_l_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_25_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1))) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1))

noncomputable def mergingStones_entail_wit_25_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1))) ,
  ((Zlength (stones_l)) = n_pre)

noncomputable def mergingStones_entail_wit_26 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1)) ” &&
  “ (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)) <= 56000) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  TT && emp 
|--
  “ ((Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int))) ” &&
  “ (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_26_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  ((Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)) <= 56000)

noncomputable def mergingStones_entail_wit_26_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)))

noncomputable def mergingStones_entail_wit_26_split_goal_3 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (__default__List_Z : _List_Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)))

noncomputable def mergingStones_entail_wit_26_split_goal_4 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (dp_l_2 : (List (List Int))) (prefix_l_2 : (List Int)) (len : Int) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1))) (PreH8 : (StoneMassesBounded stones_l n_pre)) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1))

noncomputable def mergingStones_return_wit_1 : Prop :=
  (
forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre)) (PreH4 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH5 : (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1))) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)))) (PreH7 : ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)))) (PreH8 : ((Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)) <= 56000)) ,
  (((dp_pre + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l_2 __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (0 : Int) (0 : Int) n_pre n_pre dp_l_2)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l_2)
|--
  EX dp_l : (List (List Int)), EX prefix_l : (List Int),
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1)) ” &&
  “ (StoneMinimumCost stones_l n_pre (Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int)))) ” &&
  “ ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int))) <= 56000) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
) \/
(
forall (dp_pre : Int) (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (StoneMassesBounded stones_l n_pre)) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1))) (PreH8 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)))) (PreH9 : ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)))) (PreH10 : ((Znth (n_pre - 1) (Znth (0 : Int) dp_l_2 __default__List_Z) (0 : Int)) <= 56000)) ,
  (((dp_pre + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l_2 __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (0 : Int) (0 : Int) n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)),
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1)) ” &&
  “ (StoneMinimumCost stones_l n_pre (Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int)))) ” &&
  “ ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l_2 __default__List_Z)) ((0 : Int))) <= 56000) ”
  &&  (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
)

noncomputable def mergingStones_partial_solve_wit_1 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre)) (PreH5 : (StoneTableShape dp_init n_pre)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ”
  &&  (((prefix_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg prefix_pre 1 (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)

noncomputable def mergingStones_partial_solve_wit_2 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l n_pre i) ” &&
  “ ((0 : Int) <= (Znth i prefix_l (0 : Int))) ” &&
  “ ((Znth i prefix_l (0 : Int)) <= 8000) ” &&
  “ (1 <= (Znth i stones_l (0 : Int))) ” &&
  “ ((Znth i stones_l (0 : Int)) <= 1000) ”
  &&  (((prefix_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - (0 : Int)) prefix_l (0 : Int))))
  ** (intArray.missing_i prefix_pre i (0 : Int) (i + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)

noncomputable def mergingStones_partial_solve_wit_3 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l n_pre i) ” &&
  “ ((0 : Int) <= (Znth i prefix_l (0 : Int))) ” &&
  “ ((Znth i prefix_l (0 : Int)) <= 8000) ” &&
  “ (1 <= (Znth i stones_l (0 : Int))) ” &&
  “ ((Znth i stones_l (0 : Int)) <= 1000) ”
  &&  (((stones_pre + (i * sizeof(INT)))) # Int |-> ((Znth i stones_l (0 : Int))))
  ** (intArray.missing_i stones_pre i (0 : Int) n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)

noncomputable def mergingStones_partial_solve_wit_4 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (dp_init : (List (List Int))) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre)) (PreH7 : (StoneTableShape dp_init n_pre)) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i)) (PreH9 : ((0 : Int) <= (Znth i prefix_l (0 : Int)))) (PreH10 : ((Znth i prefix_l (0 : Int)) <= 8000)) (PreH11 : (1 <= (Znth i stones_l (0 : Int)))) (PreH12 : ((Znth i stones_l (0 : Int)) <= 1000)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg prefix_pre (i + 1) (n_pre + 1))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StoneTableShape dp_init n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l n_pre i) ” &&
  “ ((0 : Int) <= (Znth i prefix_l (0 : Int))) ” &&
  “ ((Znth i prefix_l (0 : Int)) <= 8000) ” &&
  “ (1 <= (Znth i stones_l (0 : Int))) ” &&
  “ ((Znth i stones_l (0 : Int)) <= 1000) ”
  &&  (((prefix_pre + ((i + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg prefix_pre ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg prefix_pre (0 : Int) (i + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_init)

noncomputable def mergingStones_partial_solve_wit_5 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (col : Int) (row : Int) (prefix_l : (List Int)) (__default__List_Z : _List_Z) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH6 : ((0 : Int) <= row)) (PreH7 : (row < n_pre)) (PreH8 : ((0 : Int) <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneZeroProgress dp_l n_pre row col)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (col < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= col) ” &&
  “ (col <= n_pre) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneZeroProgress dp_l n_pre row col) ”
  &&  (((dp_pre + (((row * n_pre) + col) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i (dp_pre + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre row (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)

noncomputable def mergingStones_partial_solve_wit_6 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((left + len) <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= ((n_pre - len) + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len left) ”
  &&  (((prefix_pre + ((((left + len) - 1) + 1) * sizeof(INT)))) # Int |-> ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int))))
  ** (intArray.missing_i prefix_pre (((left + len) - 1) + 1) (0 : Int) (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)

noncomputable def mergingStones_partial_solve_wit_7 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_l : (List (List Int))) (prefix_l : (List Int)) (left : Int) (len : Int) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= ((n_pre - len) + 1))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1))) (PreH10 : (StoneMassesBounded stones_l n_pre)) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ ((left + len) <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= ((n_pre - len) + 1)) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ ((Zlength (prefix_l)) = (n_pre + 1)) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len left) ”
  &&  (((prefix_pre + (left * sizeof(INT)))) # Int |-> ((Znth left prefix_l (0 : Int))))
  ** (intArray.missing_i prefix_pre left (0 : Int) (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)

noncomputable def mergingStones_partial_solve_wit_8 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH12 : (2 <= interval_sum)) (PreH13 : (interval_sum <= 8000)) (PreH14 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH15 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH16 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH17 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH18 : (StoneMassesBounded stones_l n_pre)) (PreH19 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left split best) ”
  &&  (((dp_pre + (((left * n_pre) + split) * sizeof(INT)))) # Int |-> ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + ((left * n_pre) * sizeof(INT))) split (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre left (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)

noncomputable def mergingStones_partial_solve_wit_9 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH17 : ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)))) (PreH18 : ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre)) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ (right < n_pre) ” &&
  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int))) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= (Znth split (Znth left dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth split (Znth left dp_l __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ ((0 : Int) <= (Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth right (Znth (split + 1) dp_l __default__List_Z) (0 : Int)) <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left split best) ”
  &&  (((dp_pre + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)

noncomputable def mergingStones_partial_solve_wit_10 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (interval_sum : Int) (best : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + len) <= n_pre)) (PreH7 : (right = ((left + len) - 1))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 56000)) (PreH15 : (StoneMassesBounded stones_l n_pre)) (PreH16 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH17 : (StoneSplitProgress stones_l dp_l n_pre len left right best)) (PreH18 : (StoneIntervalMin stones_l left right best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < n_pre) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 56000) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left right best) ” &&
  “ (StoneIntervalMin stones_l left right best) ”
  &&  (((dp_pre + (((left * n_pre) + right) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i (dp_pre + ((left * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre left (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)

noncomputable def mergingStones_partial_solve_wit_11 : Prop :=
  forall (dp_pre : Int) (prefix_pre : Int) (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre)) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1))) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH7 : ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)))) (PreH8 : ((Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)) <= 56000)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full dp_pre n_pre n_pre dp_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (StoneMassesBounded stones_l n_pre) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1)) ” &&
  “ (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int))) ” &&
  “ ((Znth (n_pre - 1) (Znth (0 : Int) dp_l __default__List_Z) (0 : Int)) <= 56000) ”
  &&  (((dp_pre + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (dp_pre + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l __default__List_Z))
  ** (SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i dp_pre (0 : Int) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full prefix_pre (n_pre + 1) prefix_l)


structure VC_Correct : Type where
  proof_of_mergingStones_safety_wit_1 : mergingStones_safety_wit_1
  proof_of_mergingStones_safety_wit_2 : mergingStones_safety_wit_2
  proof_of_mergingStones_safety_wit_3 : mergingStones_safety_wit_3
  proof_of_mergingStones_safety_wit_4 : mergingStones_safety_wit_4
  proof_of_mergingStones_safety_wit_5 : mergingStones_safety_wit_5
  proof_of_mergingStones_safety_wit_7 : mergingStones_safety_wit_7
  proof_of_mergingStones_safety_wit_8 : mergingStones_safety_wit_8
  proof_of_mergingStones_safety_wit_9 : mergingStones_safety_wit_9
  proof_of_mergingStones_safety_wit_10 : mergingStones_safety_wit_10
  proof_of_mergingStones_safety_wit_11 : mergingStones_safety_wit_11
  proof_of_mergingStones_safety_wit_12 : mergingStones_safety_wit_12
  proof_of_mergingStones_safety_wit_13 : mergingStones_safety_wit_13
  proof_of_mergingStones_safety_wit_14 : mergingStones_safety_wit_14
  proof_of_mergingStones_safety_wit_15 : mergingStones_safety_wit_15
  proof_of_mergingStones_safety_wit_16 : mergingStones_safety_wit_16
  proof_of_mergingStones_safety_wit_17 : mergingStones_safety_wit_17
  proof_of_mergingStones_safety_wit_18 : mergingStones_safety_wit_18
  proof_of_mergingStones_safety_wit_19 : mergingStones_safety_wit_19
  proof_of_mergingStones_safety_wit_21 : mergingStones_safety_wit_21
  proof_of_mergingStones_safety_wit_22 : mergingStones_safety_wit_22
  proof_of_mergingStones_safety_wit_23 : mergingStones_safety_wit_23
  proof_of_mergingStones_safety_wit_24 : mergingStones_safety_wit_24
  proof_of_mergingStones_safety_wit_25 : mergingStones_safety_wit_25
  proof_of_mergingStones_safety_wit_26 : mergingStones_safety_wit_26
  proof_of_mergingStones_safety_wit_27 : mergingStones_safety_wit_27
  proof_of_mergingStones_safety_wit_28 : mergingStones_safety_wit_28
  proof_of_mergingStones_safety_wit_29 : mergingStones_safety_wit_29
  proof_of_mergingStones_safety_wit_30 : mergingStones_safety_wit_30
  proof_of_mergingStones_safety_wit_31 : mergingStones_safety_wit_31
  proof_of_mergingStones_safety_wit_32 : mergingStones_safety_wit_32
  proof_of_mergingStones_safety_wit_33 : mergingStones_safety_wit_33
  proof_of_mergingStones_safety_wit_34 : mergingStones_safety_wit_34
  proof_of_mergingStones_safety_wit_35 : mergingStones_safety_wit_35
  proof_of_mergingStones_safety_wit_36 : mergingStones_safety_wit_36
  proof_of_mergingStones_safety_wit_37 : mergingStones_safety_wit_37
  proof_of_mergingStones_entail_wit_10 : mergingStones_entail_wit_10
  proof_of_mergingStones_entail_wit_12 : mergingStones_entail_wit_12
  proof_of_mergingStones_entail_wit_15 : mergingStones_entail_wit_15
  proof_of_mergingStones_partial_solve_wit_1 : mergingStones_partial_solve_wit_1
  proof_of_mergingStones_partial_solve_wit_2 : mergingStones_partial_solve_wit_2
  proof_of_mergingStones_partial_solve_wit_3 : mergingStones_partial_solve_wit_3
  proof_of_mergingStones_partial_solve_wit_4 : mergingStones_partial_solve_wit_4
  proof_of_mergingStones_partial_solve_wit_5 : mergingStones_partial_solve_wit_5
  proof_of_mergingStones_partial_solve_wit_6 : mergingStones_partial_solve_wit_6
  proof_of_mergingStones_partial_solve_wit_7 : mergingStones_partial_solve_wit_7
  proof_of_mergingStones_partial_solve_wit_8 : mergingStones_partial_solve_wit_8
  proof_of_mergingStones_partial_solve_wit_9 : mergingStones_partial_solve_wit_9
  proof_of_mergingStones_partial_solve_wit_10 : mergingStones_partial_solve_wit_10
  proof_of_mergingStones_partial_solve_wit_11 : mergingStones_partial_solve_wit_11
  proof_of_mergingStones_safety_wit_6 : mergingStones_safety_wit_6
  proof_of_mergingStones_safety_wit_20 : mergingStones_safety_wit_20
  proof_of_mergingStones_entail_wit_1 : mergingStones_entail_wit_1
  proof_of_mergingStones_entail_wit_2 : mergingStones_entail_wit_2
  proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3
  proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4
  proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5
  proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6
  proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7
  proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8
  proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9
  proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11
  proof_of_mergingStones_entail_wit_13 : mergingStones_entail_wit_13
  proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14
  proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16
  proof_of_mergingStones_entail_wit_17 : mergingStones_entail_wit_17
  proof_of_mergingStones_entail_wit_18 : mergingStones_entail_wit_18
  proof_of_mergingStones_entail_wit_19_1 : mergingStones_entail_wit_19_1
  proof_of_mergingStones_entail_wit_19_2 : mergingStones_entail_wit_19_2
  proof_of_mergingStones_entail_wit_20 : mergingStones_entail_wit_20
  proof_of_mergingStones_entail_wit_21 : mergingStones_entail_wit_21
  proof_of_mergingStones_entail_wit_22 : mergingStones_entail_wit_22
  proof_of_mergingStones_entail_wit_23 : mergingStones_entail_wit_23
  proof_of_mergingStones_entail_wit_24 : mergingStones_entail_wit_24
  proof_of_mergingStones_entail_wit_25 : mergingStones_entail_wit_25
  proof_of_mergingStones_entail_wit_26 : mergingStones_entail_wit_26
  proof_of_mergingStones_return_wit_1 : mergingStones_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_goal
