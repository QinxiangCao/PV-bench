import SimpleC.SL.SeparationLogic

import Algorithms.lcs_n.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.lcs_n.lean.groundtruth.lcs_n_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance lcs_n_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def lcs_n_safety_wit_1 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stride" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_full table_pre ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def lcs_n_safety_wit_2 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stride" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_full table_pre ((n_pre + 1) * (n_pre + 1)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_3 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stride" ) )) # Int |-> ((n_pre + 1)))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_full table_pre ((n_pre + 1) * (n_pre + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lcs_n_safety_wit_4 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def lcs_n_safety_wit_5 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lcs_n_safety_wit_6 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) (replace_Znth ((stride * i)) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def lcs_n_safety_wit_7 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) (replace_Znth ((stride * i)) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_8 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_9 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : ((0 : Int) <= j)) (PreH2 : (j < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lcs_n_safety_wit_10 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : ((0 : Int) <= j)) (PreH2 : (j < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) ,
  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def lcs_n_safety_wit_11 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : ((0 : Int) <= j)) (PreH2 : (j < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) ,
  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_12 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_13 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table table_l n_pre i)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_14 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def lcs_n_safety_wit_15 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def lcs_n_safety_wit_16 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_17 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_18 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (((stride * i) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + j)) ”

noncomputable def lcs_n_safety_wit_19 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def lcs_n_safety_wit_20 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l_2 n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) + 1)) ”

noncomputable def lcs_n_safety_wit_21 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (((stride * (i - 1)) + (j - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * (i - 1)) + (j - 1))) ”

noncomputable def lcs_n_safety_wit_22 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def lcs_n_safety_wit_23 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((stride * (i - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * (i - 1))) ”

noncomputable def lcs_n_safety_wit_24 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def lcs_n_safety_wit_25 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_26 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_27 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_28 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (((stride * (i - 1)) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * (i - 1)) + j)) ”

noncomputable def lcs_n_safety_wit_29 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((stride * (i - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * (i - 1))) ”

noncomputable def lcs_n_safety_wit_30 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def lcs_n_safety_wit_31 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_32 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (((stride * i) + (j - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + (j - 1))) ”

noncomputable def lcs_n_safety_wit_33 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def lcs_n_safety_wit_34 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def lcs_n_safety_wit_35 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_36 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
|--
  “ (((stride * i) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + j)) ”

noncomputable def lcs_n_safety_wit_37 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def lcs_n_safety_wit_38 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
|--
  “ (((stride * i) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + j)) ”

noncomputable def lcs_n_safety_wit_39 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def lcs_n_safety_wit_40 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (i : Int) (j : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1))) (PreH11 : ((j + 1) <= (n_pre + 1))) (PreH12 : ((0 : Int) <= ((stride * i) + (j + 1)))) (PreH13 : (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def lcs_n_safety_wit_41 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (i : Int) (j : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1))) (PreH11 : ((j + 1) <= (n_pre + 1))) (PreH12 : ((0 : Int) <= ((stride * i) + (j + 1)))) (PreH13 : (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_42 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def lcs_n_safety_wit_43 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lcs_n_safety_wit_44 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH2 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride = (n_pre + 1))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) ,
  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (((stride * n_pre) + n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * n_pre) + n_pre)) ”

noncomputable def lcs_n_safety_wit_45 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH2 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride = (n_pre + 1))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) ,
  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((stride * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * n_pre)) ”

noncomputable def lcs_n_entail_wit_1 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_full table_pre ((n_pre + 1) * (n_pre + 1)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ ((n_pre + 1) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((n_pre + 1) * (0 : Int))) ” &&
  “ (((n_pre + 1) * (0 : Int)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
) \/
(
forall (table_pre : Int) (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (intArray.undef_full table_pre ((n_pre + 1) * (n_pre + 1)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((n_pre + 1) * (0 : Int))) ” &&
  “ (((n_pre + 1) * (0 : Int)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre (0 : Int)) ”
  &&  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
)

noncomputable def lcs_n_entail_wit_2 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre i) ”
  &&  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre + 1))) (PreH15 : ((0 : Int) <= (stride * i))) (PreH16 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  TT && emp 
|--
  “ (((n_pre + 1) * i) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre + 1))) (PreH15 : ((0 : Int) <= (stride * i))) (PreH16 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  (((n_pre + 1) * i) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def lcs_n_entail_wit_3 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) ,
  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) (replace_Znth ((stride * i)) ((Some ((0 : Int)))) (mixed_table_2)))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * (i + 1))) ” &&
  “ ((stride * (i + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre (i + 1)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= (((Zlength (xs)) + 1) * (i + 1))) ” &&
  “ ((((Zlength (xs)) + 1) * (i + 1)) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNColumnProgress (replace_Znth ((((Zlength (xs)) + 1) * i)) ((Some ((0 : Int)))) (mixed_table_2)) table_l (Zlength (xs)) (i + 1)) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_4 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table table_l n_pre 1) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= ((Zlength (xs)) + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table_2 table_l (Zlength (xs)) 1) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_5 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((0 : Int) <= j) ” &&
  “ (j < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (stride <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (stride >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table table_l n_pre j) ”
  &&  ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)

noncomputable def lcs_n_entail_wit_6 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : ((0 : Int) <= j)) (PreH2 : (j < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1))) (PreH15 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) ,
  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table_2)))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table table_l n_pre (j + 1)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : ((0 : Int) <= j)) (PreH2 : (j < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1))) (PreH15 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= ((Zlength (xs)) + 1)) ” &&
  “ (LCSNBoundaryProgress (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table_2)) table_l (Zlength (xs)) (j + 1)) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_7 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * 1)) ” &&
  “ ((stride * 1) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre 1) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= (((Zlength (xs)) + 1) * 1)) ” &&
  “ ((((Zlength (xs)) + 1) * 1) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) 1) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_8 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + 1)) ” &&
  “ (((stride * i) + 1) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i 1) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= ((((Zlength (xs)) + 1) * i) + 1)) ” &&
  “ (((((Zlength (xs)) + 1) * i) + 1) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l (Zlength (xs)) i 1) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_9 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  TT && emp 
|--
  “ ((((n_pre + 1) * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((((n_pre + 1) * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((((n_pre + 1) * i) + j) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((((n_pre + 1) * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def lcs_n_entail_wit_9_split_goal_2 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((((n_pre + 1) * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def lcs_n_entail_wit_9_split_goal_3 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  ((((n_pre + 1) * i) + j) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def lcs_n_entail_wit_10_1 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_3 : (List (Option Int))) (table_l_3 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_3) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (intArray.undef_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((((n_pre + 1) * i) + j) + 1))
  ** (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |-> (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) + 1)))
  ** (((table_pre + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_3)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
) \/
(
forall (table_pre : Int) (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_3 : (List (Option Int))) (table_l_3 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) <= INT_MAX)) (PreH2 : (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) + 1) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) >= INT_MIN)) (PreH4 : (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) + 1) >= INT_MIN)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j)) (PreH10 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_3) (None)) = None)) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))))))) (PreH12 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))))) (PreH13 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) <= n_pre)) (PreH14 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : ((0 : Int) <= (j - 1))) (PreH18 : ((j - 1) < n_pre)) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH22 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH24 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH26 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre >= INT_MIN)) (PreH29 : (j <= n_pre)) (PreH30 : (stride = (n_pre + 1))) (PreH31 : ((0 : Int) <= n_pre)) (PreH32 : (n_pre <= 1000)) (PreH33 : ((Zlength (xs)) = n_pre)) (PreH34 : ((Zlength (ys)) = n_pre)) (PreH35 : (1 <= i)) (PreH36 : (i <= n_pre)) (PreH37 : (1 <= j)) (PreH38 : (j <= (n_pre + 1))) (PreH39 : ((0 : Int) <= ((stride * i) + j))) (PreH40 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH41 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |-> (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int))) + 1)))
  ** (((table_pre + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_3)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ”
  &&  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
)

noncomputable def lcs_n_entail_wit_10_2 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_3 : (List (Option Int))) (table_l_3 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_3) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (intArray.undef_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((((n_pre + 1) * i) + j) + 1))
  ** (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_3)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
) \/
(
forall (table_pre : Int) (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_3 : (List (Option Int))) (table_l_3 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j)) (PreH11 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_3) (None)) = None)) (PreH12 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))))))) (PreH13 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))))) (PreH14 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : ((0 : Int) <= (j - 1))) (PreH18 : ((j - 1) < n_pre)) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH22 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH24 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH26 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre >= INT_MIN)) (PreH29 : (j <= n_pre)) (PreH30 : (stride = (n_pre + 1))) (PreH31 : ((0 : Int) <= n_pre)) (PreH32 : (n_pre <= 1000)) (PreH33 : ((Zlength (xs)) = n_pre)) (PreH34 : ((Zlength (ys)) = n_pre)) (PreH35 : (1 <= i)) (PreH36 : (i <= n_pre)) (PreH37 : (1 <= j)) (PreH38 : (j <= (n_pre + 1))) (PreH39 : ((0 : Int) <= ((stride * i) + j))) (PreH40 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH41 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_3)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ”
  &&  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
)

noncomputable def lcs_n_entail_wit_10_3 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_3 : (List (Option Int))) (table_l_3 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_3) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (intArray.undef_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((((n_pre + 1) * i) + j) + 1))
  ** (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_3)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
) \/
(
forall (table_pre : Int) (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_3 : (List (Option Int))) (table_l_3 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j)) (PreH11 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_3) (None)) = None)) (PreH12 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int))))))) (PreH13 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_3) ((0 : Int))))))) (PreH14 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH15 : ((0 : Int) <= (i - 1))) (PreH16 : ((i - 1) < n_pre)) (PreH17 : ((0 : Int) <= (j - 1))) (PreH18 : ((j - 1) < n_pre)) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH22 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH24 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH26 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre >= INT_MIN)) (PreH29 : (j <= n_pre)) (PreH30 : (stride = (n_pre + 1))) (PreH31 : ((0 : Int) <= n_pre)) (PreH32 : (n_pre <= 1000)) (PreH33 : ((Zlength (xs)) = n_pre)) (PreH34 : ((Zlength (ys)) = n_pre)) (PreH35 : (1 <= i)) (PreH36 : (i <= n_pre)) (PreH37 : (1 <= j)) (PreH38 : (j <= (n_pre + 1))) (PreH39 : ((0 : Int) <= ((stride * i) + j))) (PreH40 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH41 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_3) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_3) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_3)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_3)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ”
  &&  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
)

noncomputable def lcs_n_entail_wit_11 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (stride : Int) (i : Int) (j : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1))) (PreH11 : ((j + 1) <= (n_pre + 1))) (PreH12 : ((0 : Int) <= ((stride * i) + (j + 1)))) (PreH13 : (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i (j + 1))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)

noncomputable def lcs_n_entail_wit_12 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * (i + 1))) ” &&
  “ ((stride * (i + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (i + 1)) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= (((Zlength (xs)) + 1) * (i + 1))) ” &&
  “ ((((Zlength (xs)) + 1) * (i + 1)) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) (i + 1)) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_13 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1)) ” &&
  “ (LCSNTableResult xs ys n_pre table_l) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
) \/
(
forall (table_pre : Int) (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) ,
  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1)) ” &&
  “ (LCSNTableResult xs ys n_pre table_l) ”
  &&  (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)
)

noncomputable def lcs_n_entail_wit_14 : Prop :=
  (
forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : (LCSNTableResult xs ys n_pre table_l)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ ((0 : Int) <= ((stride * n_pre) + n_pre)) ” &&
  “ (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1)) ” &&
  “ (LCSNTableResult xs ys n_pre table_l) ”
  &&  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (stride >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (stride = (n_pre + 1))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (xs)) = n_pre)) (PreH9 : ((Zlength (ys)) = n_pre)) (PreH10 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH11 : (LCSNTableResult xs ys n_pre table_l)) ,
  TT && emp 
|--
  “ ((((n_pre + 1) * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def lcs_n_entail_wit_14_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (stride >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (stride = (n_pre + 1))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (xs)) = n_pre)) (PreH9 : ((Zlength (ys)) = n_pre)) (PreH10 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH11 : (LCSNTableResult xs ys n_pre table_l)) ,
  ((((n_pre + 1) * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def lcs_n_return_wit_1 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l_2 : (List Int)) (stride : Int) (PreH1 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH2 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride = (n_pre + 1))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l_2 n_pre (n_pre + 1))) (PreH9 : (LCSNTableResult xs ys n_pre table_l_2)) ,
  (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l_2)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  EX table_l : (List Int),
  “ (LCSNTableResult xs ys n_pre table_l) ” &&
  “ ((Znth ((stride * n_pre) + n_pre) table_l_2 (0 : Int)) = (Znth ((((n_pre + 1) * n_pre) + n_pre)) (table_l) ((0 : Int)))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)

noncomputable def lcs_n_partial_solve_wit_1 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre i) ”
  &&  (((table_pre + ((stride * i) * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i table_pre (stride * i) (0 : Int) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)

noncomputable def lcs_n_partial_solve_wit_2 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : ((0 : Int) <= j)) (PreH2 : (j < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((0 : Int) <= j) ” &&
  “ (j < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (stride <= INT_MAX) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (stride >= INT_MIN) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table table_l n_pre j) ”
  &&  (((table_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i table_pre j (0 : Int) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)

noncomputable def lcs_n_partial_solve_wit_3 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((x_pre + ((i - 1) * sizeof(INT)))) # Int |-> ((Znth (i - 1) xs (0 : Int))))
  ** (intArray.missing_i x_pre (i - 1) (0 : Int) n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)

noncomputable def lcs_n_partial_solve_wit_4 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((y_pre + ((j - 1) * sizeof(INT)))) # Int |-> ((Znth (j - 1) ys (0 : Int))))
  ** (intArray.missing_i y_pre (j - 1) (0 : Int) n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)

noncomputable def lcs_n_partial_solve_wit_5_pure : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”

noncomputable def lcs_n_partial_solve_wit_5_aux : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_5 : Prop := lcs_n_partial_solve_wit_5_pure -> lcs_n_partial_solve_wit_5_aux

noncomputable def lcs_n_partial_solve_wit_6 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((table_pre + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_7 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH8 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH10 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i table_pre ((stride * i) + j) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (((table_pre + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_8_pure : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "table" ) )) # Ptr |-> (table_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”

noncomputable def lcs_n_partial_solve_wit_8_aux : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (intArray.mixed_full table_pre ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_8 : Prop := lcs_n_partial_solve_wit_8_pure -> lcs_n_partial_solve_wit_8_aux

noncomputable def lcs_n_partial_solve_wit_9 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_10 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH8 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH10 : ((0 : Int) <= (i - 1))) (PreH11 : ((i - 1) < n_pre)) (PreH12 : ((0 : Int) <= (j - 1))) (PreH13 : ((j - 1) < n_pre)) (PreH14 : ((0 : Int) <= ((stride * i) + j))) (PreH15 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH17 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH19 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH21 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1))) (PreH26 : ((0 : Int) <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1))) (PreH34 : ((0 : Int) <= ((stride * i) + j))) (PreH35 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (((table_pre + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_11 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
|--
  “ ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i table_pre ((stride * i) + j) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_12 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH9 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH10 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH11 : ((0 : Int) <= (i - 1))) (PreH12 : ((i - 1) < n_pre)) (PreH13 : ((0 : Int) <= (j - 1))) (PreH14 : ((j - 1) < n_pre)) (PreH15 : ((0 : Int) <= ((stride * i) + j))) (PreH16 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH18 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH20 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH22 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1))) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1))) (PreH35 : ((0 : Int) <= ((stride * i) + j))) (PreH36 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) ,
  (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.undef_seg table_pre (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
|--
  “ ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ”
  &&  (((table_pre + (((stride * i) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i table_pre ((stride * i) + j) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (((table_pre + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((table_pre + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg table_pre (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg table_pre ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)

noncomputable def lcs_n_partial_solve_wit_13 : Prop :=
  forall (table_pre : Int) (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH2 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (stride = (n_pre + 1))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full table_pre ((n_pre + 1) * (n_pre + 1)) table_l)
|--
  “ ((0 : Int) <= ((stride * n_pre) + n_pre)) ” &&
  “ (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1)) ” &&
  “ (LCSNTableResult xs ys n_pre table_l) ”
  &&  (((table_pre + (((stride * n_pre) + n_pre) * sizeof(INT)))) # Int |-> ((Znth ((stride * n_pre) + n_pre) table_l (0 : Int))))
  ** (intArray.missing_i table_pre ((stride * n_pre) + n_pre) (0 : Int) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)

noncomputable def lcs_n_which_implies_wit_1 : Prop :=
  (
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (table_l_2 : (List Int)) (mixed_table_2 : (List (Option Int))) (i : Int) (j : Int) (table : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (intArray.mixed_full table ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre) ”
  &&  (intArray.mixed_seg table (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((table + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg table ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg table (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (table_l_2 : (List Int)) (mixed_table_2 : (List (Option Int))) (i : Int) (j : Int) (table : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (intArray.mixed_full table ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre) ”
  &&  (intArray.mixed_seg table (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((table + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg table ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg table (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
)

noncomputable def lcs_n_which_implies_wit_2 : Prop :=
  (
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (table_l_2 : (List Int)) (mixed_table_2 : (List (Option Int))) (i : Int) (j : Int) (table : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (intArray.mixed_full table ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ”
  &&  (intArray.mixed_seg table (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((table + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg table ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((table + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg table (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (table_l_2 : (List Int)) (mixed_table_2 : (List (Option Int))) (i : Int) (j : Int) (table : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) ,
  (intArray.mixed_full table ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ”
  &&  (intArray.mixed_seg table (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((table + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg table ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((table + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg table (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg table ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
)


structure VC_Correct : Type where
  proof_of_lcs_n_safety_wit_1 : lcs_n_safety_wit_1
  proof_of_lcs_n_safety_wit_2 : lcs_n_safety_wit_2
  proof_of_lcs_n_safety_wit_3 : lcs_n_safety_wit_3
  proof_of_lcs_n_safety_wit_4 : lcs_n_safety_wit_4
  proof_of_lcs_n_safety_wit_5 : lcs_n_safety_wit_5
  proof_of_lcs_n_safety_wit_6 : lcs_n_safety_wit_6
  proof_of_lcs_n_safety_wit_7 : lcs_n_safety_wit_7
  proof_of_lcs_n_safety_wit_8 : lcs_n_safety_wit_8
  proof_of_lcs_n_safety_wit_9 : lcs_n_safety_wit_9
  proof_of_lcs_n_safety_wit_10 : lcs_n_safety_wit_10
  proof_of_lcs_n_safety_wit_11 : lcs_n_safety_wit_11
  proof_of_lcs_n_safety_wit_12 : lcs_n_safety_wit_12
  proof_of_lcs_n_safety_wit_13 : lcs_n_safety_wit_13
  proof_of_lcs_n_safety_wit_14 : lcs_n_safety_wit_14
  proof_of_lcs_n_safety_wit_15 : lcs_n_safety_wit_15
  proof_of_lcs_n_safety_wit_16 : lcs_n_safety_wit_16
  proof_of_lcs_n_safety_wit_17 : lcs_n_safety_wit_17
  proof_of_lcs_n_safety_wit_18 : lcs_n_safety_wit_18
  proof_of_lcs_n_safety_wit_19 : lcs_n_safety_wit_19
  proof_of_lcs_n_safety_wit_20 : lcs_n_safety_wit_20
  proof_of_lcs_n_safety_wit_21 : lcs_n_safety_wit_21
  proof_of_lcs_n_safety_wit_22 : lcs_n_safety_wit_22
  proof_of_lcs_n_safety_wit_23 : lcs_n_safety_wit_23
  proof_of_lcs_n_safety_wit_24 : lcs_n_safety_wit_24
  proof_of_lcs_n_safety_wit_25 : lcs_n_safety_wit_25
  proof_of_lcs_n_safety_wit_26 : lcs_n_safety_wit_26
  proof_of_lcs_n_safety_wit_27 : lcs_n_safety_wit_27
  proof_of_lcs_n_safety_wit_28 : lcs_n_safety_wit_28
  proof_of_lcs_n_safety_wit_29 : lcs_n_safety_wit_29
  proof_of_lcs_n_safety_wit_30 : lcs_n_safety_wit_30
  proof_of_lcs_n_safety_wit_31 : lcs_n_safety_wit_31
  proof_of_lcs_n_safety_wit_32 : lcs_n_safety_wit_32
  proof_of_lcs_n_safety_wit_33 : lcs_n_safety_wit_33
  proof_of_lcs_n_safety_wit_34 : lcs_n_safety_wit_34
  proof_of_lcs_n_safety_wit_35 : lcs_n_safety_wit_35
  proof_of_lcs_n_safety_wit_36 : lcs_n_safety_wit_36
  proof_of_lcs_n_safety_wit_37 : lcs_n_safety_wit_37
  proof_of_lcs_n_safety_wit_38 : lcs_n_safety_wit_38
  proof_of_lcs_n_safety_wit_39 : lcs_n_safety_wit_39
  proof_of_lcs_n_safety_wit_40 : lcs_n_safety_wit_40
  proof_of_lcs_n_safety_wit_41 : lcs_n_safety_wit_41
  proof_of_lcs_n_safety_wit_42 : lcs_n_safety_wit_42
  proof_of_lcs_n_safety_wit_43 : lcs_n_safety_wit_43
  proof_of_lcs_n_safety_wit_44 : lcs_n_safety_wit_44
  proof_of_lcs_n_safety_wit_45 : lcs_n_safety_wit_45
  proof_of_lcs_n_entail_wit_5 : lcs_n_entail_wit_5
  proof_of_lcs_n_entail_wit_11 : lcs_n_entail_wit_11
  proof_of_lcs_n_return_wit_1 : lcs_n_return_wit_1
  proof_of_lcs_n_partial_solve_wit_1 : lcs_n_partial_solve_wit_1
  proof_of_lcs_n_partial_solve_wit_2 : lcs_n_partial_solve_wit_2
  proof_of_lcs_n_partial_solve_wit_3 : lcs_n_partial_solve_wit_3
  proof_of_lcs_n_partial_solve_wit_4 : lcs_n_partial_solve_wit_4
  proof_of_lcs_n_partial_solve_wit_5_pure : lcs_n_partial_solve_wit_5_pure
  proof_of_lcs_n_partial_solve_wit_5 : lcs_n_partial_solve_wit_5
  proof_of_lcs_n_partial_solve_wit_6 : lcs_n_partial_solve_wit_6
  proof_of_lcs_n_partial_solve_wit_7 : lcs_n_partial_solve_wit_7
  proof_of_lcs_n_partial_solve_wit_8_pure : lcs_n_partial_solve_wit_8_pure
  proof_of_lcs_n_partial_solve_wit_8 : lcs_n_partial_solve_wit_8
  proof_of_lcs_n_partial_solve_wit_9 : lcs_n_partial_solve_wit_9
  proof_of_lcs_n_partial_solve_wit_10 : lcs_n_partial_solve_wit_10
  proof_of_lcs_n_partial_solve_wit_11 : lcs_n_partial_solve_wit_11
  proof_of_lcs_n_partial_solve_wit_12 : lcs_n_partial_solve_wit_12
  proof_of_lcs_n_partial_solve_wit_13 : lcs_n_partial_solve_wit_13
  proof_of_lcs_n_entail_wit_1 : lcs_n_entail_wit_1
  proof_of_lcs_n_entail_wit_2 : lcs_n_entail_wit_2
  proof_of_lcs_n_entail_wit_3 : lcs_n_entail_wit_3
  proof_of_lcs_n_entail_wit_4 : lcs_n_entail_wit_4
  proof_of_lcs_n_entail_wit_6 : lcs_n_entail_wit_6
  proof_of_lcs_n_entail_wit_7 : lcs_n_entail_wit_7
  proof_of_lcs_n_entail_wit_8 : lcs_n_entail_wit_8
  proof_of_lcs_n_entail_wit_9 : lcs_n_entail_wit_9
  proof_of_lcs_n_entail_wit_10_1 : lcs_n_entail_wit_10_1
  proof_of_lcs_n_entail_wit_10_2 : lcs_n_entail_wit_10_2
  proof_of_lcs_n_entail_wit_10_3 : lcs_n_entail_wit_10_3
  proof_of_lcs_n_entail_wit_12 : lcs_n_entail_wit_12
  proof_of_lcs_n_entail_wit_13 : lcs_n_entail_wit_13
  proof_of_lcs_n_entail_wit_14 : lcs_n_entail_wit_14
  proof_of_lcs_n_which_implies_wit_1 : lcs_n_which_implies_wit_1
  proof_of_lcs_n_which_implies_wit_2 : lcs_n_which_implies_wit_2

end Algorithms.lcs_n.lean.groundtruth.lcs_n_goal
