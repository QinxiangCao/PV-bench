import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance catalan_numbers_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def id_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (((x_pre * (n_pre + 1)) + y_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((x_pre * (n_pre + 1)) + y_pre)) ”

noncomputable def id_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((x_pre * (n_pre + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_pre * (n_pre + 1))) ”

noncomputable def id_safety_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def id_safety_wit_4 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def id_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  TT && emp 
|--
  “ (((x_pre * (n_pre + 1)) + y_pre) = ((x_pre * (n_pre + 1)) + y_pre)) ” &&
  “ ((0 : Int) <= ((x_pre * (n_pre + 1)) + y_pre)) ” &&
  “ (((x_pre * (n_pre + 1)) + y_pre) <= ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  TT && emp 
|--
  “ (((x_pre * (n_pre + 1)) + y_pre) <= ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def id_return_wit_1_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  (((x_pre * (n_pre + 1)) + y_pre) <= ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_safety_wit_1 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** (intArray.undef_full f_pre ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_2 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackRowsDone n_pre table i)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg f_pre (0 : Int) (i * (n_pre + 1)) table)
  ** (intArray.undef_seg f_pre (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_3 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= (n_pre + 1))) (PreH8 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_4 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_5 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (i ≠ (0 : Int))) (PreH2 : (j <= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_6 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = (0 : Int))) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_7 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = (0 : Int))) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solve_safety_wit_8 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = (0 : Int))) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_9 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = (0 : Int))) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_10 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int)))) ”
) \/
(
forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int)))) ”
)

noncomputable def solve_safety_wit_10_split_goal_1 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int))) <= INT_MAX) ”

noncomputable def solve_safety_wit_10_split_goal_2 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval_3)) (PreH9 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((INT_MIN) <= ((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int)))) ”

noncomputable def solve_safety_wit_11 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_12 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solve_safety_wit_13 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_14 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_15 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH14 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH16 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH17 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH18 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH19 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def solve_safety_wit_16 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH14 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH16 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH17 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH18 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH19 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_17 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int)))) (PreH8 : (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int)))) (PreH9 : (StackRowProgress n_pre table i (j + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) table)
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_18 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (StackRowsDone n_pre table (i + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg f_pre (0 : Int) ((i + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg f_pre ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solve_safety_wit_19 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH4 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH5 : (StackRowsDone n_pre table (n_pre + 1))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_entail_wit_1 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  (intArray.undef_full f_pre ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackRowsDone n_pre table (0 : Int)) ”
  &&  (intArray.seg f_pre (0 : Int) ((0 : Int) * (n_pre + 1)) table)
  ** (intArray.undef_seg f_pre ((0 : Int) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (f_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  (intArray.undef_full f_pre ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackRowsDone n_pre table (0 : Int)) ”
  &&  (intArray.seg f_pre (0 : Int) ((0 : Int) * (n_pre + 1)) table)
  ** (intArray.undef_seg f_pre ((0 : Int) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
)

noncomputable def solve_entail_wit_2 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackRowsDone n_pre table_2 i)) ,
  (intArray.seg f_pre (0 : Int) (i * (n_pre + 1)) table_2)
  ** (intArray.undef_seg f_pre (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackRowProgress n_pre table i (0 : Int)) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + (0 : Int)) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + (0 : Int)) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackRowsDone n_pre table_2 i)) ,
  (intArray.seg f_pre (0 : Int) (i * (n_pre + 1)) table_2)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackRowProgress n_pre table i (0 : Int)) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + (0 : Int)) table)
)

noncomputable def solve_entail_wit_3 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  TT && emp 
|--
  “ ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) < ((i * (n_pre + 1)) + (0 : Int))) ” &&
  “ (((i * (n_pre + 1)) + (0 : Int)) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def solve_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) < ((i * (n_pre + 1)) + (0 : Int)))

noncomputable def solve_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  (((i * (n_pre + 1)) + (0 : Int)) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_entail_wit_4 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  TT && emp 
|--
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def solve_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))

noncomputable def solve_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackRowProgress n_pre table_2 i j)) ,
  (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_entail_wit_5_1 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table_2 i j)) ,
  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ ((1 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int))) ” &&
  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int))) ” &&
  “ (StackRowProgress n_pre table i (j + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) table)
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table_2 i j)) ,
  TT && emp 
|--
  “ (StackRowProgress n_pre (table_2 ++ (1 :: (@List.nil Int))) (0 : Int) (j + 1)) ” &&
  “ (StackCellCorrect n_pre (0 : Int) j (Znth (((0 : Int) * (n_pre + 1)) + j) (table_2 ++ (1 :: (@List.nil Int))) (0 : Int))) ” &&
  “ (StackCellBound (0 : Int) j (Znth (((0 : Int) * (n_pre + 1)) + j) (table_2 ++ (1 :: (@List.nil Int))) (0 : Int))) ”
  &&  emp
)

noncomputable def solve_entail_wit_5_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table_2 i j)) ,
  (StackRowProgress n_pre (table_2 ++ (1 :: (@List.nil Int))) (0 : Int) (j + 1))

noncomputable def solve_entail_wit_5_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table_2 i j)) ,
  (StackCellCorrect n_pre (0 : Int) j (Znth (((0 : Int) * (n_pre + 1)) + j) (table_2 ++ (1 :: (@List.nil Int))) (0 : Int)))

noncomputable def solve_entail_wit_5_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table_2 i j)) ,
  (StackCellBound (0 : Int) j (Znth (((0 : Int) * (n_pre + 1)) + j) (table_2 ++ (1 :: (@List.nil Int))) (0 : Int)))

noncomputable def solve_entail_wit_5_2 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table_2 i j)) ,
  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ ((Znth (retval_2 - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int))) ” &&
  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int))) ” &&
  “ (StackRowProgress n_pre table i (j + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) table)
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table_2 i j)) ,
  TT && emp 
|--
  “ (StackRowProgress n_pre (table_2 ++ ((Znth ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))) i ((0 : Int) + 1)) ” &&
  “ (StackCellCorrect n_pre i (0 : Int) (Znth ((i * (n_pre + 1)) + (0 : Int)) (table_2 ++ ((Znth ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))) (0 : Int))) ” &&
  “ (StackCellBound i (0 : Int) (Znth ((i * (n_pre + 1)) + (0 : Int)) (table_2 ++ ((Znth ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))) (0 : Int))) ”
  &&  emp
)

noncomputable def solve_entail_wit_5_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table_2 i j)) ,
  (StackRowProgress n_pre (table_2 ++ ((Znth ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))) i ((0 : Int) + 1))

noncomputable def solve_entail_wit_5_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table_2 i j)) ,
  (StackCellCorrect n_pre i (0 : Int) (Znth ((i * (n_pre + 1)) + (0 : Int)) (table_2 ++ ((Znth ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))) (0 : Int)))

noncomputable def solve_entail_wit_5_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table_2 i j)) ,
  (StackCellBound i (0 : Int) (Znth ((i * (n_pre + 1)) + (0 : Int)) (table_2 ++ ((Znth ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))) (0 : Int)))

noncomputable def solve_entail_wit_5_3 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table_2 i j)) ,
  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ (((Znth (retval_2 - (0 : Int)) table_2 (0 : Int)) + (Znth (retval_3 - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int))) ” &&
  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) table (0 : Int))) ” &&
  “ (StackRowProgress n_pre table i (j + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) table)
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table_2 i j)) ,
  TT && emp 
|--
  “ (StackRowProgress n_pre (table_2 ++ (((Znth ((((i - 1) * (n_pre + 1)) + (j + 1)) - (0 : Int)) table_2 (0 : Int)) + (Znth (((i * (n_pre + 1)) + (j - 1)) - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))) i (j + 1)) ” &&
  “ (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) (table_2 ++ (((Znth ((((i - 1) * (n_pre + 1)) + (j + 1)) - (0 : Int)) table_2 (0 : Int)) + (Znth (((i * (n_pre + 1)) + (j - 1)) - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))) (0 : Int))) ” &&
  “ (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) (table_2 ++ (((Znth ((((i - 1) * (n_pre + 1)) + (j + 1)) - (0 : Int)) table_2 (0 : Int)) + (Znth (((i * (n_pre + 1)) + (j - 1)) - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))) (0 : Int))) ”
  &&  emp
)

noncomputable def solve_entail_wit_5_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table_2 i j)) ,
  (StackRowProgress n_pre (table_2 ++ (((Znth ((((i - 1) * (n_pre + 1)) + (j + 1)) - (0 : Int)) table_2 (0 : Int)) + (Znth (((i * (n_pre + 1)) + (j - 1)) - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))) i (j + 1))

noncomputable def solve_entail_wit_5_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table_2 i j)) ,
  (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) (table_2 ++ (((Znth ((((i - 1) * (n_pre + 1)) + (j + 1)) - (0 : Int)) table_2 (0 : Int)) + (Znth (((i * (n_pre + 1)) + (j - 1)) - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))) (0 : Int)))

noncomputable def solve_entail_wit_5_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table_2 i j)) ,
  (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) (table_2 ++ (((Znth ((((i - 1) * (n_pre + 1)) + (j + 1)) - (0 : Int)) table_2 (0 : Int)) + (Znth (((i * (n_pre + 1)) + (j - 1)) - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))) (0 : Int)))

noncomputable def solve_entail_wit_6 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) table_2 (0 : Int)))) (PreH8 : (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) table_2 (0 : Int)))) (PreH9 : (StackRowProgress n_pre table_2 i (j + 1))) ,
  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) table_2)
  ** (intArray.undef_seg f_pre (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackRowProgress n_pre table i (j + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + (j + 1)) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (StackCellBound i j (Znth ((i * (n_pre + 1)) + j) table_2 (0 : Int)))) (PreH8 : (StackCellCorrect n_pre i j (Znth ((i * (n_pre + 1)) + j) table_2 (0 : Int)))) (PreH9 : (StackRowProgress n_pre table_2 i (j + 1))) ,
  (intArray.seg f_pre (0 : Int) (((i * (n_pre + 1)) + j) + 1) table_2)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackRowProgress n_pre table i (j + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
)

noncomputable def solve_entail_wit_7 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= (n_pre + 1))) (PreH8 : (StackRowProgress n_pre table_2 i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (StackRowsDone n_pre table (i + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) ((i + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg f_pre ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
) \/
(
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= (n_pre + 1))) (PreH8 : (StackRowProgress n_pre table_2 i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (StackRowsDone n_pre table (i + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) ((i + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg f_pre ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
)

noncomputable def solve_entail_wit_8 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (StackRowsDone n_pre table_2 (i + 1))) ,
  (intArray.seg f_pre (0 : Int) ((i + 1) * (n_pre + 1)) table_2)
  ** (intArray.undef_seg f_pre ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (StackRowsDone n_pre table (i + 1)) ”
  &&  (intArray.seg f_pre (0 : Int) ((i + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg f_pre ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_entail_wit_9 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackRowsDone n_pre table_2 i)) ,
  (intArray.seg f_pre (0 : Int) (i * (n_pre + 1)) table_2)
  ** (intArray.undef_seg f_pre (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackRowsDone n_pre table (n_pre + 1)) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)
) \/
(
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackRowsDone n_pre table_2 i)) ,
  (intArray.seg f_pre (0 : Int) (i * (n_pre + 1)) table_2)
  ** (intArray.undef_seg f_pre (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackRowsDone n_pre table (n_pre + 1)) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)
)

noncomputable def solve_return_wit_1 : Prop :=
  (
forall (f_pre : Int) (n_pre : Int) (table_2 : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH7 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : (StackRowsDone n_pre table_2 (n_pre + 1))) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table_2 (0 : Int)))) ,
  (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table_2)
|--
  EX table : (List Int),
  “ (StackSequenceCount n_pre (Znth retval table_2 (0 : Int))) ” &&
  “ (StackRowsDone n_pre table (n_pre + 1)) ”
  &&  (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH7 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : (StackRowsDone n_pre table_2 (n_pre + 1))) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table_2 (0 : Int)))) ,
  TT && emp 
|--
  “ (StackSequenceCount n_pre (Znth ((n_pre * (n_pre + 1)) + (0 : Int)) table_2 (0 : Int))) ”
  &&  emp
)

noncomputable def solve_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH7 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : (StackRowsDone n_pre table_2 (n_pre + 1))) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table_2 (0 : Int)))) ,
  (StackSequenceCount n_pre (Znth ((n_pre * (n_pre + 1)) + (0 : Int)) table_2 (0 : Int)))

noncomputable def solve_partial_solve_wit_1_pure : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (i = (0 : Int))) (PreH2 : (j <= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_1_aux : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (i = (0 : Int))) (PreH2 : (j <= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (i = (0 : Int)) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_1 : Prop := solve_partial_solve_wit_1_pure -> solve_partial_solve_wit_1_aux

noncomputable def solve_partial_solve_wit_2 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (i = (0 : Int))) (PreH5 : (j <= n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 7)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (n_pre + 1))) (PreH12 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (i = (0 : Int)) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i f_pre retval ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)

noncomputable def solve_partial_solve_wit_3_pure : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (j = (0 : Int))) (PreH6 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH7 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH9 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH10 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_3_aux : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (j = (0 : Int))) (PreH6 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH7 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH9 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH10 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_3 : Prop := solve_partial_solve_wit_3_pure -> solve_partial_solve_wit_3_aux

noncomputable def solve_partial_solve_wit_4_pure : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = (0 : Int))) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_4_aux : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (j = (0 : Int))) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_4 : Prop := solve_partial_solve_wit_4_pure -> solve_partial_solve_wit_4_aux

noncomputable def solve_partial_solve_wit_5 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (((f_pre + (retval_2 * sizeof(INT)))) # Int |-> ((Znth (retval_2 - (0 : Int)) table (0 : Int))))
  ** (intArray.missing_i f_pre retval_2 (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_6 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (j = (0 : Int))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH13 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH15 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i f_pre retval ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)

noncomputable def solve_partial_solve_wit_7_pure : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH12 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_7_aux : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH12 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_7 : Prop := solve_partial_solve_wit_7_pure -> solve_partial_solve_wit_7_aux

noncomputable def solve_partial_solve_wit_8_pure : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_8_aux : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_8 : Prop := solve_partial_solve_wit_8_pure -> solve_partial_solve_wit_8_aux

noncomputable def solve_partial_solve_wit_9 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH14 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH16 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH17 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH18 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH19 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (((f_pre + (retval_2 * sizeof(INT)))) # Int |-> ((Znth (retval_2 - (0 : Int)) table (0 : Int))))
  ** (intArray.missing_i f_pre retval_2 (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_10_pure : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH14 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH16 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH17 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH18 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH19 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_10_aux : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval = ((i * (n_pre + 1)) + j))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 7)) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH14 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH16 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH17 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH18 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH19 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) <= (n_pre + 1)) ” &&
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_10 : Prop := solve_partial_solve_wit_10_pure -> solve_partial_solve_wit_10_aux

noncomputable def solve_partial_solve_wit_11 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (retval_3 = ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ ((0 : Int) <= retval_3) ” &&
  “ (retval_3 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (((f_pre + (retval_3 * sizeof(INT)))) # Int |-> ((Znth (retval_3 - (0 : Int)) table (0 : Int))))
  ** (intArray.missing_i f_pre retval_3 (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_partial_solve_wit_12 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : ((0 : Int) <= retval_3)) (PreH3 : (retval_3 <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH5 : ((0 : Int) <= retval_2)) (PreH6 : (retval_2 <= ((n_pre + 1) * (n_pre + 1)))) (PreH7 : (retval = ((i * (n_pre + 1)) + j))) (PreH8 : ((0 : Int) <= retval)) (PreH9 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= n_pre)) (PreH11 : (n_pre <= 7)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH17 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH19 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH20 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH21 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH22 : (StackRowProgress n_pre table i j)) ,
  (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg f_pre ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  “ (retval_3 = ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ ((0 : Int) <= retval_3) ” &&
  “ (retval_3 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackRowProgress n_pre table i j) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i f_pre retval ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.seg f_pre (0 : Int) ((i * (n_pre + 1)) + j) table)

noncomputable def solve_partial_solve_wit_13_pure : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH4 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH5 : (StackRowsDone n_pre table (n_pre + 1))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "f" ) )) # Ptr |-> (f_pre))
  ** (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_13_aux : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH4 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH5 : (StackRowsDone n_pre table (n_pre + 1))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackRowsDone n_pre table (n_pre + 1)) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)

noncomputable def solve_partial_solve_wit_13 : Prop := solve_partial_solve_wit_13_pure -> solve_partial_solve_wit_13_aux

noncomputable def solve_partial_solve_wit_14 : Prop :=
  forall (f_pre : Int) (n_pre : Int) (table : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= ((n_pre + 1) * (n_pre + 1)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH7 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : (StackRowsDone n_pre table (n_pre + 1))) (PreH9 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full f_pre ((n_pre + 1) * (n_pre + 1)) table)
|--
  “ (retval = ((n_pre * (n_pre + 1)) + (0 : Int))) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackRowsDone n_pre table (n_pre + 1)) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (((f_pre + (retval * sizeof(INT)))) # Int |-> ((Znth retval table (0 : Int))))
  ** (intArray.missing_i f_pre retval (0 : Int) ((n_pre + 1) * (n_pre + 1)) table)


structure VC_Correct : Type where
  proof_of_id_safety_wit_1 : id_safety_wit_1
  proof_of_id_safety_wit_2 : id_safety_wit_2
  proof_of_id_safety_wit_3 : id_safety_wit_3
  proof_of_id_safety_wit_4 : id_safety_wit_4
  proof_of_solve_safety_wit_1 : solve_safety_wit_1
  proof_of_solve_safety_wit_2 : solve_safety_wit_2
  proof_of_solve_safety_wit_3 : solve_safety_wit_3
  proof_of_solve_safety_wit_4 : solve_safety_wit_4
  proof_of_solve_safety_wit_5 : solve_safety_wit_5
  proof_of_solve_safety_wit_6 : solve_safety_wit_6
  proof_of_solve_safety_wit_7 : solve_safety_wit_7
  proof_of_solve_safety_wit_8 : solve_safety_wit_8
  proof_of_solve_safety_wit_9 : solve_safety_wit_9
  proof_of_solve_safety_wit_11 : solve_safety_wit_11
  proof_of_solve_safety_wit_12 : solve_safety_wit_12
  proof_of_solve_safety_wit_13 : solve_safety_wit_13
  proof_of_solve_safety_wit_14 : solve_safety_wit_14
  proof_of_solve_safety_wit_15 : solve_safety_wit_15
  proof_of_solve_safety_wit_16 : solve_safety_wit_16
  proof_of_solve_safety_wit_17 : solve_safety_wit_17
  proof_of_solve_safety_wit_18 : solve_safety_wit_18
  proof_of_solve_safety_wit_19 : solve_safety_wit_19
  proof_of_solve_entail_wit_8 : solve_entail_wit_8
  proof_of_solve_partial_solve_wit_1_pure : solve_partial_solve_wit_1_pure
  proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1
  proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2
  proof_of_solve_partial_solve_wit_3_pure : solve_partial_solve_wit_3_pure
  proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3
  proof_of_solve_partial_solve_wit_4_pure : solve_partial_solve_wit_4_pure
  proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4
  proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5
  proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6
  proof_of_solve_partial_solve_wit_7_pure : solve_partial_solve_wit_7_pure
  proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7
  proof_of_solve_partial_solve_wit_8_pure : solve_partial_solve_wit_8_pure
  proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8
  proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9
  proof_of_solve_partial_solve_wit_10_pure : solve_partial_solve_wit_10_pure
  proof_of_solve_partial_solve_wit_10 : solve_partial_solve_wit_10
  proof_of_solve_partial_solve_wit_11 : solve_partial_solve_wit_11
  proof_of_solve_partial_solve_wit_12 : solve_partial_solve_wit_12
  proof_of_solve_partial_solve_wit_13_pure : solve_partial_solve_wit_13_pure
  proof_of_solve_partial_solve_wit_13 : solve_partial_solve_wit_13
  proof_of_solve_partial_solve_wit_14 : solve_partial_solve_wit_14
  proof_of_id_return_wit_1 : id_return_wit_1
  proof_of_solve_safety_wit_10 : solve_safety_wit_10
  proof_of_solve_entail_wit_1 : solve_entail_wit_1
  proof_of_solve_entail_wit_2 : solve_entail_wit_2
  proof_of_solve_entail_wit_3 : solve_entail_wit_3
  proof_of_solve_entail_wit_4 : solve_entail_wit_4
  proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1
  proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2
  proof_of_solve_entail_wit_5_3 : solve_entail_wit_5_3
  proof_of_solve_entail_wit_6 : solve_entail_wit_6
  proof_of_solve_entail_wit_7 : solve_entail_wit_7
  proof_of_solve_entail_wit_9 : solve_entail_wit_9
  proof_of_solve_return_wit_1 : solve_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_goal
