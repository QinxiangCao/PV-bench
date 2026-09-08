import SimpleC.SL.SeparationLogic

import Algorithms.multiple_knapsack.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.multiple_knapsack.lean.groundtruth.multiple_knapsack_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance multiple_knapsack_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def multipleKnapsack_safety_wit_1 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_full dp_pre (capacity_pre + 1))
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_2 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l j)) (PreH14 : (MKZeroPrefixSemantics dp_l j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l)
  ** (intArray.undef_seg dp_pre j (capacity_pre + 1))
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_3 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l j)) (PreH14 : (MKZeroPrefixSemantics dp_l j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.seg dp_pre (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (j + 1) (capacity_pre + 1))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def multipleKnapsack_safety_wit_4 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH10 : (MKZeroPrefixSafety dp_l (capacity_pre + 1))) (PreH11 : (MKZeroPrefixSemantics dp_l (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l)) (PreH14 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_5 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH17 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_6 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH19 : (MKCopyPrefixSafety dp_l old_l j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) (replace_Znth (j) ((Znth j dp_l (0 : Int))) (old_l)))
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def multipleKnapsack_safety_wit_7 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH25 : (MKDPValueBound old_l capacity_pre)) (PreH26 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH27 : (MKCopyPrefixSafety dp_l old_l (capacity_pre + 1) capacity_pre)) (PreH28 : (MKCopyPrefixSemantics dp_l old_l (capacity_pre + 1))) (PreH29 : (MKItemResidueProgressSafety old_l dp_l (0 : Int) w cnt capacity_pre)) (PreH30 : (MKItemResidueProgressSemantics old_l dp_l (0 : Int) w v cnt capacity_pre)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "r" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_8 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r > capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH30 : (MKDPValueBound old_l capacity_pre)) (PreH31 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l dp_l r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH34 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ False ”

noncomputable def multipleKnapsack_safety_wit_9 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH30 : (MKDPValueBound old_l capacity_pre)) (PreH31 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l dp_l r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH34 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "head" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_10 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH30 : (MKDPValueBound old_l capacity_pre)) (PreH31 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l dp_l r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH34 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "tail" ) )) # Int |->_)
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_11 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH30 : (MKDPValueBound old_l capacity_pre)) (PreH31 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l dp_l r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH34 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_12 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos old_l (0 : Int)) - (k * v))) ”
) \/
(
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos old_l (0 : Int)) - (k * v))) ”
)

noncomputable def multipleKnapsack_safety_wit_12_split_goal_1 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= INT_MAX) ”

noncomputable def multipleKnapsack_safety_wit_12_split_goal_2 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((INT_MIN) <= ((Znth pos old_l (0 : Int)) - (k * v))) ”

noncomputable def multipleKnapsack_safety_wit_13 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((k * v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k * v)) ”

noncomputable def multipleKnapsack_safety_wit_14 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (MKDPValueBound old_l capacity_pre)) (PreH44 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH48 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((k - cnt) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k - cnt)) ”

noncomputable def multipleKnapsack_safety_wit_15 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth head qidx_l (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH44 : (MKDPValueBound old_l capacity_pre)) (PreH45 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((head + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (head + 1)) ”

noncomputable def multipleKnapsack_safety_wit_16 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH44 : (MKDPValueBound old_l capacity_pre)) (PreH45 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def multipleKnapsack_safety_wit_17 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH44 : (MKDPValueBound old_l capacity_pre)) (PreH45 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def multipleKnapsack_safety_wit_18 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH45 : (MKDPValueBound old_l capacity_pre)) (PreH46 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def multipleKnapsack_safety_wit_19 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH44 : (MKDPValueBound old_l capacity_pre)) (PreH45 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
|--
  “ ((tail + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail + 1)) ”

noncomputable def multipleKnapsack_safety_wit_20 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH45 : (MKDPValueBound old_l capacity_pre)) (PreH46 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
|--
  “ ((tail + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail + 1)) ”

noncomputable def multipleKnapsack_safety_wit_21 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (MKDPValueBound old_l capacity_pre)) (PreH43 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
|--
  “ (((Znth head qval_l (0 : Int)) + (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth head qval_l (0 : Int)) + (k * v))) ”

noncomputable def multipleKnapsack_safety_wit_22 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (MKDPValueBound old_l capacity_pre)) (PreH43 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
|--
  “ ((k * v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k * v)) ”

noncomputable def multipleKnapsack_safety_wit_23 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (MKDPValueBound old_l capacity_pre)) (PreH43 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full dp_pre (capacity_pre + 1) (replace_Znth (pos) (((Znth head qval_l (0 : Int)) + (k * v))) (dp_l)))
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def multipleKnapsack_safety_wit_24 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (MKDPValueBound old_l capacity_pre)) (PreH43 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full dp_pre (capacity_pre + 1) (replace_Znth (pos) (((Znth head qval_l (0 : Int)) + (k * v))) (dp_l)))
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> ((k + 1)))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
|--
  “ ((pos + w) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + w)) ”

noncomputable def multipleKnapsack_safety_wit_25 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (k : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : ((0 : Int) <= k)) (PreH27 : (k <= (capacity_pre + 1))) (PreH28 : ((0 : Int) <= head)) (PreH29 : (head <= tail)) (PreH30 : (tail <= k)) (PreH31 : (tail <= (capacity_pre + 1))) (PreH32 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH33 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH34 : (MKDPValueBound old_l capacity_pre)) (PreH35 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH36 : (MKItemResidueProgressSafety old_l dp_l (r + 1) w cnt capacity_pre)) (PreH37 : (MKItemResidueProgressSemantics old_l dp_l (r + 1) w v cnt capacity_pre)) (PreH38 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((r + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r + 1)) ”

noncomputable def multipleKnapsack_safety_wit_26 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l)) (PreH25 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "old" ) )) # Ptr |-> (old_pre))
  ** ((( &( "q_idx" ) )) # Ptr |-> (q_idx_pre))
  ** ((( &( "q_val" ) )) # Ptr |-> (q_val_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def multipleKnapsack_entail_wit_1 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH9 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_full dp_pre (capacity_pre + 1))
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre) ” &&
  “ (MKZeroPrefixSafety dp_l (0 : Int)) ” &&
  “ (MKZeroPrefixSemantics dp_l (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg dp_pre (0 : Int) (0 : Int) dp_l)
  ** (intArray.undef_seg dp_pre (0 : Int) (capacity_pre + 1))
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH9 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKZeroPrefixSemantics (@List.nil Int) (0 : Int)) ” &&
  “ (MKZeroPrefixSafety (@List.nil Int) (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_1_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH9 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_1_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH9 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKZeroPrefixSemantics (@List.nil Int) (0 : Int))

noncomputable def multipleKnapsack_entail_wit_1_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH9 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKZeroPrefixSafety (@List.nil Int) (0 : Int))

noncomputable def multipleKnapsack_entail_wit_1_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH9 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def multipleKnapsack_entail_wit_2 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l_2 j)) (PreH14 : (MKZeroPrefixSemantics dp_l_2 j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.seg dp_pre (0 : Int) (j + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (j + 1) (capacity_pre + 1))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (j + 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre) ” &&
  “ (MKZeroPrefixSafety dp_l (j + 1)) ” &&
  “ (MKZeroPrefixSemantics dp_l (j + 1)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg dp_pre (0 : Int) (j + 1) dp_l)
  ** (intArray.undef_seg dp_pre (j + 1) (capacity_pre + 1))
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l_2 j)) (PreH14 : (MKZeroPrefixSemantics dp_l_2 j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ (MKZeroPrefixSemantics (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1)) ” &&
  “ (MKZeroPrefixSafety (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1)) ” &&
  “ ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_2_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l_2 j)) (PreH14 : (MKZeroPrefixSemantics dp_l_2 j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKZeroPrefixSemantics (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1))

noncomputable def multipleKnapsack_entail_wit_2_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l_2 j)) (PreH14 : (MKZeroPrefixSemantics dp_l_2 j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKZeroPrefixSafety (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1))

noncomputable def multipleKnapsack_entail_wit_2_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l_2 j)) (PreH14 : (MKZeroPrefixSemantics dp_l_2 j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1))

noncomputable def multipleKnapsack_entail_wit_3 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l_2 j)) (PreH14 : (MKZeroPrefixSemantics dp_l_2 j)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l_2)
  ** (intArray.undef_seg dp_pre j (capacity_pre + 1))
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre) ” &&
  “ (MKZeroPrefixSafety dp_l (capacity_pre + 1)) ” &&
  “ (MKZeroPrefixSemantics dp_l (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
) \/
(
forall (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l_2 j)) (PreH14 : (MKZeroPrefixSemantics dp_l_2 j)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.seg dp_pre (0 : Int) j dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre) ” &&
  “ (MKZeroPrefixSafety dp_l (capacity_pre + 1)) ” &&
  “ (MKZeroPrefixSemantics dp_l (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full dp_pre (capacity_pre + 1) dp_l)
)

noncomputable def multipleKnapsack_entail_wit_4 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH10 : (MKZeroPrefixSafety dp_l_2 (capacity_pre + 1))) (PreH11 : (MKZeroPrefixSemantics dp_l_2 (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l_2)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH10 : (MKZeroPrefixSafety dp_l_2 (capacity_pre + 1))) (PreH11 : (MKZeroPrefixSemantics dp_l_2 (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l_2)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ ((Zlength (qval0)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx0)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old0)) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_4_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH10 : (MKZeroPrefixSafety dp_l_2 (capacity_pre + 1))) (PreH11 : (MKZeroPrefixSemantics dp_l_2 (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l_2)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_4_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH10 : (MKZeroPrefixSafety dp_l_2 (capacity_pre + 1))) (PreH11 : (MKZeroPrefixSemantics dp_l_2 (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l_2)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength (qval0)) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_4_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH10 : (MKZeroPrefixSafety dp_l_2 (capacity_pre + 1))) (PreH11 : (MKZeroPrefixSemantics dp_l_2 (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l_2)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength (qidx0)) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_4_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH10 : (MKZeroPrefixSafety dp_l_2 (capacity_pre + 1))) (PreH11 : (MKZeroPrefixSemantics dp_l_2 (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l (0 : Int) capacity_pre dp_l_2)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength (old0)) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_5 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSafety dp_l old_l (0 : Int) capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKCopyPrefixSemantics dp_l_2 old_l_2 (0 : Int)) ” &&
  “ (MKCopyPrefixSafety dp_l_2 old_l_2 (0 : Int) capacity_pre) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_5_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_5_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKCopyPrefixSemantics dp_l_2 old_l_2 (0 : Int))

noncomputable def multipleKnapsack_entail_wit_5_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKCopyPrefixSafety dp_l_2 old_l_2 (0 : Int) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_6 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)))
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSafety dp_l old_l (j + 1) capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l (j + 1)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ (MKCopyPrefixSemantics dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)) (j + 1)) ” &&
  “ (MKCopyPrefixSafety dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)) (j + 1) capacity_pre) ” &&
  “ ((Zlength ((replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)))) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKCopyPrefixSemantics dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)) (j + 1))

noncomputable def multipleKnapsack_entail_wit_6_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKCopyPrefixSafety dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)) (j + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_7 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i weights_l (0 : Int)) = (Znth i weights_l (0 : Int))) ” &&
  “ ((Znth i values_l (0 : Int)) = (Znth i values_l (0 : Int))) ” &&
  “ ((Znth i counts_l (0 : Int)) = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= (Znth i weights_l (0 : Int))) ” &&
  “ ((Znth i weights_l (0 : Int)) <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (Znth i values_l (0 : Int))) ” &&
  “ ((Znth i values_l (0 : Int)) <= 1000) ” &&
  “ ((0 : Int) <= (Znth i counts_l (0 : Int))) ” &&
  “ ((Znth i counts_l (0 : Int)) <= capacity_pre) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ (MKCopyPrefixSafety dp_l old_l (capacity_pre + 1) capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l (capacity_pre + 1)) ” &&
  “ (MKItemResidueProgressSafety old_l dp_l (0 : Int) (Znth i weights_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ (MKItemResidueProgressSemantics old_l dp_l (0 : Int) (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ (MKItemResidueProgressSafety old_l_2 dp_l_2 (0 : Int) (Znth i weights_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l_2 old_l_2 (capacity_pre + 1)) ” &&
  “ (MKCopyPrefixSafety dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre) ” &&
  “ (MKTransitionValueBound old_l_2 (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ (MKDPValueBound old_l_2 capacity_pre) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_7_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResidueProgressSafety old_l_2 dp_l_2 (0 : Int) (Znth i weights_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKCopyPrefixSemantics dp_l_2 old_l_2 (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_7_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKCopyPrefixSafety dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKTransitionValueBound old_l_2 (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH19 : (MKCopyPrefixSafety dp_l_2 old_l_2 j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKDPValueBound old_l_2 capacity_pre)

noncomputable def multipleKnapsack_entail_wit_8 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH25 : (MKDPValueBound old_l_2 capacity_pre)) (PreH26 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH27 : (MKCopyPrefixSafety dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre)) (PreH28 : (MKCopyPrefixSemantics dp_l_2 old_l_2 (capacity_pre + 1))) (PreH29 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (0 : Int) w cnt capacity_pre)) (PreH30 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) w v cnt capacity_pre)) (PreH31 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= w) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResidueProgressSafety old_l dp_l (0 : Int) w cnt capacity_pre) ” &&
  “ (MKItemResidueProgressSemantics old_l dp_l (0 : Int) w v cnt capacity_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH25 : (MKDPValueBound old_l_2 capacity_pre)) (PreH26 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH27 : (MKCopyPrefixSafety dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre)) (PreH28 : (MKCopyPrefixSemantics dp_l_2 old_l_2 (capacity_pre + 1))) (PreH29 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (0 : Int) w cnt capacity_pre)) (PreH30 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) w v cnt capacity_pre)) (PreH31 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l_2) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_8_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH25 : (MKDPValueBound old_l_2 capacity_pre)) (PreH26 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH27 : (MKCopyPrefixSafety dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre)) (PreH28 : (MKCopyPrefixSemantics dp_l_2 old_l_2 (capacity_pre + 1))) (PreH29 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (0 : Int) w cnt capacity_pre)) (PreH30 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) w v cnt capacity_pre)) (PreH31 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_8_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH25 : (MKDPValueBound old_l_2 capacity_pre)) (PreH26 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH27 : (MKCopyPrefixSafety dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre)) (PreH28 : (MKCopyPrefixSemantics dp_l_2 old_l_2 (capacity_pre + 1))) (PreH29 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (0 : Int) w cnt capacity_pre)) (PreH30 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) w v cnt capacity_pre)) (PreH31 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)

noncomputable def multipleKnapsack_entail_wit_8_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH25 : (MKDPValueBound old_l_2 capacity_pre)) (PreH26 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH27 : (MKCopyPrefixSafety dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre)) (PreH28 : (MKCopyPrefixSemantics dp_l_2 old_l_2 (capacity_pre + 1))) (PreH29 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (0 : Int) w cnt capacity_pre)) (PreH30 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) w v cnt capacity_pre)) (PreH31 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKDPTableSafety weights_l i capacity_pre old_l_2)

noncomputable def multipleKnapsack_entail_wit_9 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH30 : (MKDPValueBound old_l_2 capacity_pre)) (PreH31 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH34 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (r = (r + ((0 : Int) * w))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (capacity_pre + w)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt (0 : Int) capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt (0 : Int) capacity_pre) ” &&
  “ (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w (0 : Int) (0 : Int) (0 : Int) capacity_pre) ” &&
  “ (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt (0 : Int) (0 : Int) (0 : Int) capacity_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH30 : (MKDPValueBound old_l_2 capacity_pre)) (PreH31 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH34 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKResidueLoopSemantics old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt (0 : Int) (0 : Int) (0 : Int) capacity_pre) ” &&
  “ (MKResidueLoopSafety old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w (0 : Int) (0 : Int) (0 : Int) capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt (0 : Int) capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt (0 : Int) capacity_pre) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_9_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH30 : (MKDPValueBound old_l_2 capacity_pre)) (PreH31 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH34 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_9_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH30 : (MKDPValueBound old_l_2 capacity_pre)) (PreH31 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH34 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKResidueLoopSemantics old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt (0 : Int) (0 : Int) (0 : Int) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_9_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH30 : (MKDPValueBound old_l_2 capacity_pre)) (PreH31 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH34 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKResidueLoopSafety old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w (0 : Int) (0 : Int) (0 : Int) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_9_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH30 : (MKDPValueBound old_l_2 capacity_pre)) (PreH31 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH34 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt (0 : Int) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_9_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH29 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH30 : (MKDPValueBound old_l_2 capacity_pre)) (PreH31 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH33 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH34 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt (0 : Int) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_10 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l_2 : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l_2)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (((Znth pos old_l (0 : Int)) - (k * v)) = ((Znth pos old_l_2 (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= (((Znth pos old_l (0 : Int)) - (k * v)) + (k * v))) ” &&
  “ ((((Znth pos old_l (0 : Int)) - (k * v)) + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l_2) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2) ” &&
  “ (MKDPValueBound old_l_2 capacity_pre) ” &&
  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l_2 dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l_2 dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l_2 qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueueDropSemantics old_l_2 qidx_l qval_l head tail r w v cnt k) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKQueueDropSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k) ” &&
  “ (MKQueueDropSafety old_l qidx_l_2 qval_l_2 head tail r w k capacity_pre) ” &&
  “ ((((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v))) ” &&
  “ (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) <= 1000000) ” &&
  “ ((-1000000) <= ((Znth (r + (k * w)) old_l (0 : Int)) - (k * v))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_10_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_10_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueDropSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k)

noncomputable def multipleKnapsack_entail_wit_10_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueDropSafety old_l qidx_l_2 qval_l_2 head tail r w k capacity_pre)

noncomputable def multipleKnapsack_entail_wit_10_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v)) <= 1000000)

noncomputable def multipleKnapsack_entail_wit_10_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((0 : Int) <= (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v)))

noncomputable def multipleKnapsack_entail_wit_10_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) <= 1000000)

noncomputable def multipleKnapsack_entail_wit_10_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((-1000000) <= ((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)))

noncomputable def multipleKnapsack_entail_wit_11 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= (head + 1)) ” &&
  “ ((head + 1) <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l (head + 1) tail r w k capacity_pre) ” &&
  “ (MKQueueDropSemantics old_l qidx_l qval_l (head + 1) tail r w v cnt k) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 (head + 1) tail r w v cnt k) ” &&
  “ (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 (head + 1) tail r w k capacity_pre) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_11_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 (head + 1) tail r w v cnt k)

noncomputable def multipleKnapsack_entail_wit_11_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 (head + 1) tail r w k capacity_pre)

noncomputable def multipleKnapsack_entail_wit_12_1 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueueAfterDropSemantics old_l qidx_l qval_l head tail r w v cnt k) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)

noncomputable def multipleKnapsack_entail_wit_12_2 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueueAfterDropSemantics old_l qidx_l qval_l head tail r w v cnt k) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)

noncomputable def multipleKnapsack_entail_wit_13 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head <= tail)) (PreH38 : (tail <= k)) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head <= tail)) (PreH38 : (tail <= k)) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_13_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head <= tail)) (PreH38 : (tail <= k)) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_13_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head <= tail)) (PreH38 : (tail <= k)) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (MKDPValueBound old_l_2 capacity_pre)) (PreH44 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH48 : (MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)

noncomputable def multipleKnapsack_entail_wit_14 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= (tail - 1)) ” &&
  “ ((tail - 1) <= k) ” &&
  “ ((tail - 1) <= (capacity_pre + 1)) ” &&
  “ ((head < (tail - 1)) -> (((0 : Int) <= ((tail - 1) - 1)) ∧ (((tail - 1) - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head (tail - 1) r w k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head (tail - 1) r w v cnt k current) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head (tail - 1) r w v cnt k current) ” &&
  “ (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head (tail - 1) r w k capacity_pre) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_14_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head (tail - 1) r w v cnt k current)

noncomputable def multipleKnapsack_entail_wit_14_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head (tail - 1) r w k capacity_pre)

noncomputable def multipleKnapsack_entail_wit_15_1 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l_2)))
  ** (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l_2)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < (tail + 1)) ” &&
  “ ((tail + 1) <= (k + 1)) ” &&
  “ ((tail + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueResultSafety old_l qidx_l qval_l head (tail + 1) r w (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKTransitionSafety old_l w cnt capacity_pre pos) ” &&
  “ (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) ” &&
  “ (MKTransitionSemantics old_l_2 w v cnt capacity_pre (r + (k * w)) ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) ” &&
  “ (MKTransitionSafety old_l_2 w cnt capacity_pre (r + (k * w))) ” &&
  “ (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSafety old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w (k + 1) capacity_pre) ” &&
  “ ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1)) ” &&
  “ ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)) <= 1000000)

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((0 : Int) <= ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)))

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKTransitionSemantics old_l_2 w v cnt capacity_pre (r + (k * w)) ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)))

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKTransitionSafety old_l_2 w cnt capacity_pre (r + (k * w)))

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueResultSafety old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_8 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_15_1_split_goal_9 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH44 : (MKDPValueBound old_l_2 capacity_pre)) (PreH45 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH50 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_15_2 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l_2)))
  ** (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l_2)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < (tail + 1)) ” &&
  “ ((tail + 1) <= (k + 1)) ” &&
  “ ((tail + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueResultSafety old_l qidx_l qval_l head (tail + 1) r w (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKTransitionSafety old_l w cnt capacity_pre pos) ” &&
  “ (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) ” &&
  “ (MKTransitionSemantics old_l_2 w v cnt capacity_pre (r + (k * w)) ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) ” &&
  “ (MKTransitionSafety old_l_2 w cnt capacity_pre (r + (k * w))) ” &&
  “ (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSafety old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w (k + 1) capacity_pre) ” &&
  “ ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1)) ” &&
  “ ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)) <= 1000000)

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((0 : Int) <= ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)))

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKTransitionSemantics old_l_2 w v cnt capacity_pre (r + (k * w)) ((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v)))

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKTransitionSafety old_l_2 w cnt capacity_pre (r + (k * w)))

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKQueueResultSafety old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_8 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_15_2_split_goal_9 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH45 : (MKDPValueBound old_l_2 capacity_pre)) (PreH46 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_16 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full dp_pre (capacity_pre + 1) (replace_Znth (pos) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)))
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ ((pos + w) = (r + ((k + 1) * w))) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (pos + w)) ” &&
  “ ((pos + w) <= (capacity_pre + w)) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= (k + 1)) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt (k + 1) capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w (k + 1) head tail capacity_pre) ” &&
  “ (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt (k + 1) head tail capacity_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKResidueLoopSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) qidx_l_2 qval_l_2 r w v cnt (k + 1) head tail capacity_pre) ” &&
  “ (MKResidueLoopSafety old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) qidx_l_2 qval_l_2 r w (k + 1) head tail capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) r w cnt (k + 1) capacity_pre) ” &&
  “ (((r + (k * w)) + w) = (r + ((k + 1) * w))) ” &&
  “ ((Zlength ((replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)))) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_16_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_16_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKResidueLoopSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) qidx_l_2 qval_l_2 r w v cnt (k + 1) head tail capacity_pre)

noncomputable def multipleKnapsack_entail_wit_16_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKResidueLoopSafety old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) qidx_l_2 qval_l_2 r w (k + 1) head tail capacity_pre)

noncomputable def multipleKnapsack_entail_wit_16_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) r w v cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_16_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResiduePrefixSafety old_l_2 (replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)) r w cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_16_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (((r + (k * w)) + w) = (r + ((k + 1) * w)))

noncomputable def multipleKnapsack_entail_wit_16_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (MKDPValueBound old_l_2 capacity_pre)) (PreH43 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l_2 qidx_l_2 qval_l_2 head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l_2 w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l_2 (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l_2 (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  ((Zlength ((replace_Znth ((r + (k * w))) (((Znth head qval_l_2 (0 : Int)) + (k * v))) (dp_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_17 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH38 : (MKDPValueBound old_l_2 capacity_pre)) (PreH39 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResidueProgressSafety old_l dp_l (r + 1) w cnt capacity_pre) ” &&
  “ (MKItemResidueProgressSemantics old_l dp_l (r + 1) w v cnt capacity_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH38 : (MKDPValueBound old_l_2 capacity_pre)) (PreH39 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1) w v cnt capacity_pre) ” &&
  “ (MKItemResidueProgressSafety old_l_2 dp_l_2 (r + 1) w cnt capacity_pre) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_17_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH38 : (MKDPValueBound old_l_2 capacity_pre)) (PreH39 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_17_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH38 : (MKDPValueBound old_l_2 capacity_pre)) (PreH39 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1) w v cnt capacity_pre)

noncomputable def multipleKnapsack_entail_wit_17_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH38 : (MKDPValueBound old_l_2 capacity_pre)) (PreH39 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l_2 dp_l_2 r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKItemResidueProgressSafety old_l_2 dp_l_2 (r + 1) w cnt capacity_pre)

noncomputable def multipleKnapsack_entail_wit_18 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (k : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : ((0 : Int) <= k)) (PreH27 : (k <= (capacity_pre + 1))) (PreH28 : ((0 : Int) <= head)) (PreH29 : (head <= tail)) (PreH30 : (tail <= k)) (PreH31 : (tail <= (capacity_pre + 1))) (PreH32 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH33 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH34 : (MKDPValueBound old_l_2 capacity_pre)) (PreH35 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH36 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (r + 1) w cnt capacity_pre)) (PreH37 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1) w v cnt capacity_pre)) (PreH38 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ ((0 : Int) <= (r + 1)) ” &&
  “ ((r + 1) <= w) ” &&
  “ ((r + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResidueProgressSafety old_l dp_l (r + 1) w cnt capacity_pre) ” &&
  “ (MKItemResidueProgressSemantics old_l dp_l (r + 1) w v cnt capacity_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (k : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : ((0 : Int) <= k)) (PreH27 : (k <= (capacity_pre + 1))) (PreH28 : ((0 : Int) <= head)) (PreH29 : (head <= tail)) (PreH30 : (tail <= k)) (PreH31 : (tail <= (capacity_pre + 1))) (PreH32 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH33 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH34 : (MKDPValueBound old_l_2 capacity_pre)) (PreH35 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH36 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (r + 1) w cnt capacity_pre)) (PreH37 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1) w v cnt capacity_pre)) (PreH38 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_18_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (k : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : ((0 : Int) <= k)) (PreH27 : (k <= (capacity_pre + 1))) (PreH28 : ((0 : Int) <= head)) (PreH29 : (head <= tail)) (PreH30 : (tail <= k)) (PreH31 : (tail <= (capacity_pre + 1))) (PreH32 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH33 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH34 : (MKDPValueBound old_l_2 capacity_pre)) (PreH35 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH36 : (MKItemResidueProgressSafety old_l_2 dp_l_2 (r + 1) w cnt capacity_pre)) (PreH37 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1) w v cnt capacity_pre)) (PreH38 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_19 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (MKDPValueBound old_l_2 capacity_pre)) (PreH30 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH31 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (MKDPValueBound old_l_2 capacity_pre)) (PreH30 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH31 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l_2) ” &&
  “ (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l_2) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_19_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (MKDPValueBound old_l_2 capacity_pre)) (PreH30 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH31 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_19_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (MKDPValueBound old_l_2 capacity_pre)) (PreH30 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH31 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l_2)

noncomputable def multipleKnapsack_entail_wit_19_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSafety weights_l i capacity_pre old_l_2)) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (MKDPValueBound old_l_2 capacity_pre)) (PreH30 : (MKTransitionValueBound old_l_2 w v cnt capacity_pre)) (PreH31 : (MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre)) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l_2)

noncomputable def multipleKnapsack_entail_wit_20 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l_2)) (PreH25 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l_2)) (PreH25 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_20_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (i : Int) (w : Int) (v : Int) (cnt : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (w = (Znth i weights_l (0 : Int)))) (PreH15 : (v = (Znth i values_l (0 : Int)))) (PreH16 : (cnt = (Znth i counts_l (0 : Int)))) (PreH17 : (1 <= w)) (PreH18 : (w <= (capacity_pre + 1))) (PreH19 : ((0 : Int) <= v)) (PreH20 : (v <= 1000)) (PreH21 : ((0 : Int) <= cnt)) (PreH22 : (cnt <= capacity_pre)) (PreH23 : (MKDPTableSafety weights_l (i + 1) capacity_pre dp_l_2)) (PreH24 : (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l_2)) (PreH25 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l (0 : Int))) ∧ ((Znth idx_2 weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx_2 values_l (0 : Int)))) ∧ ((Znth idx_2 values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx_2 counts_l (0 : Int)))) ∧ ((Znth idx_2 counts_l (0 : Int)) <= capacity_pre)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))

noncomputable def multipleKnapsack_entail_wit_21 : Prop :=
  (
forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l n_pre capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l n_pre capacity_pre dp_l) ” &&
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l (0 : Int))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  TT && emp 
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l_2 (0 : Int))) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l n_pre capacity_pre dp_l_2) ” &&
  “ (MKDPTableSafety weights_l n_pre capacity_pre dp_l_2) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_21_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l_2 (0 : Int)))

noncomputable def multipleKnapsack_entail_wit_21_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKDPTableSemantics weights_l values_l counts_l n_pre capacity_pre dp_l_2)

noncomputable def multipleKnapsack_entail_wit_21_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSafety weights_l i capacity_pre dp_l_2)) (PreH16 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH17 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (MKDPTableSafety weights_l n_pre capacity_pre dp_l_2)

noncomputable def multipleKnapsack_return_wit_1 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l_2 : (List Int)) (old_l_2 : (List Int)) (qidx_l_2 : (List Int)) (qval_l_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l n_pre capacity_pre dp_l_2)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l n_pre capacity_pre dp_l_2)) (PreH14 : (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l_2 (0 : Int)))) ,
  (intArray.full dp_pre (capacity_pre + 1) dp_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l_2)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l_2)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l_2)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l_2 (0 : Int))) ” &&
  “ (MKDPTableSafety weights_l n_pre capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l n_pre capacity_pre dp_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_1 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (capacity_pre + 1))) (PreH12 : (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre)) (PreH13 : (MKZeroPrefixSafety dp_l j)) (PreH14 : (MKZeroPrefixSemantics dp_l j)) (PreH15 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l)
  ** (intArray.undef_seg dp_pre j (capacity_pre + 1))
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = j) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKScratchArraysSafety old0 qidx0 qval0 capacity_pre) ” &&
  “ (MKZeroPrefixSafety dp_l j) ” &&
  “ (MKZeroPrefixSemantics dp_l j) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (j + 1) (capacity_pre + 1))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg dp_pre (0 : Int) j dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old0)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx0)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval0)

noncomputable def multipleKnapsack_partial_solve_wit_2 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH19 : (MKCopyPrefixSafety dp_l old_l j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSafety dp_l old_l j capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int |-> ((Znth j dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre j (0 : Int) (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_3 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH19 : (MKCopyPrefixSafety dp_l old_l j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSafety dp_l old_l j capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((old_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i old_pre j (0 : Int) (capacity_pre + 1) old_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_4 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH19 : (MKCopyPrefixSafety dp_l old_l j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (j > capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSafety dp_l old_l j capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((weights_pre + (i * sizeof(INT)))) # Int |-> ((Znth i weights_l (0 : Int))))
  ** (intArray.missing_i weights_pre i (0 : Int) n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_5 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH19 : (MKCopyPrefixSafety dp_l old_l j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (j > capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSafety dp_l old_l j capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((values_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values_l (0 : Int))))
  ** (intArray.missing_i values_pre i (0 : Int) n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_6 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSafety weights_l i capacity_pre dp_l)) (PreH18 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH19 : (MKCopyPrefixSafety dp_l old_l j capacity_pre)) (PreH20 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (j > capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSafety dp_l old_l j capacity_pre) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((counts_pre + (i * sizeof(INT)))) # Int |-> ((Znth i counts_l (0 : Int))))
  ** (intArray.missing_i counts_pre i (0 : Int) n_pre counts_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_7 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH37 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH38 : (MKDPValueBound old_l capacity_pre)) (PreH39 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH40 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH41 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH42 : (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w k head tail capacity_pre)) (PreH43 : (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre)) (PreH44 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (pos <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= (capacity_pre + w)) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKResidueLoopSafety old_l dp_l qidx_l qval_l r w k head tail capacity_pre) ” &&
  “ (MKResidueLoopSemantics old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((old_pre + (pos * sizeof(INT)))) # Int |-> ((Znth pos old_l (0 : Int))))
  ** (intArray.missing_i old_pre pos (0 : Int) (capacity_pre + 1) old_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_8 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (MKDPValueBound old_l capacity_pre)) (PreH44 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH45 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH48 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((q_idx_pre + (head * sizeof(INT)))) # Int |-> ((Znth head qidx_l (0 : Int))))
  ** (intArray.missing_i q_idx_pre head (0 : Int) (capacity_pre + 1) qidx_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_9 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH44 : (MKDPValueBound old_l capacity_pre)) (PreH45 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((q_val_pre + ((tail - 1) * sizeof(INT)))) # Int |-> ((Znth (tail - 1) qval_l (0 : Int))))
  ** (intArray.missing_i q_val_pre (tail - 1) (0 : Int) (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)

noncomputable def multipleKnapsack_partial_solve_wit_10 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH44 : (MKDPValueBound old_l capacity_pre)) (PreH45 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (head >= tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((q_idx_pre + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i q_idx_pre tail (0 : Int) (capacity_pre + 1) qidx_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)

noncomputable def multipleKnapsack_partial_solve_wit_11 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH45 : (MKDPValueBound old_l capacity_pre)) (PreH46 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
|--
  “ ((Znth (tail - 1) qval_l (0 : Int)) > current) ” &&
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((q_idx_pre + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i q_idx_pre tail (0 : Int) (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)

noncomputable def multipleKnapsack_partial_solve_wit_12 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH42 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH43 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH44 : (MKDPValueBound old_l capacity_pre)) (PreH45 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH46 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH47 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH48 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH49 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ (head >= tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((q_val_pre + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i q_val_pre tail (0 : Int) (capacity_pre + 1) qval_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)

noncomputable def multipleKnapsack_partial_solve_wit_13 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1))))) (PreH43 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH44 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH45 : (MKDPValueBound old_l capacity_pre)) (PreH46 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH47 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH48 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH49 : (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre)) (PreH50 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
|--
  “ ((Znth (tail - 1) qval_l (0 : Int)) > current) ” &&
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ ((head < tail) -> (((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < (capacity_pre + 1)))) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSafety old_l qidx_l qval_l head tail r w k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((q_val_pre + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i q_val_pre tail (0 : Int) (capacity_pre + 1) qval_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)

noncomputable def multipleKnapsack_partial_solve_wit_14 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (MKDPValueBound old_l capacity_pre)) (PreH43 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (k + 1)) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKTransitionSafety old_l w cnt capacity_pre pos) ” &&
  “ (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((q_val_pre + (head * sizeof(INT)))) # Int |-> ((Znth head qval_l (0 : Int))))
  ** (intArray.missing_i q_val_pre head (0 : Int) (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)

noncomputable def multipleKnapsack_partial_solve_wit_15 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (i : Int) (r : Int) (w : Int) (v : Int) (cnt : Int) (pos : Int) (k : Int) (current : Int) (head : Int) (tail : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < w)) (PreH16 : (r <= capacity_pre)) (PreH17 : (w = (Znth i weights_l (0 : Int)))) (PreH18 : (v = (Znth i values_l (0 : Int)))) (PreH19 : (cnt = (Znth i counts_l (0 : Int)))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1))) (PreH22 : ((0 : Int) <= v)) (PreH23 : (v <= 1000)) (PreH24 : ((0 : Int) <= cnt)) (PreH25 : (cnt <= capacity_pre)) (PreH26 : (pos = (r + (k * w)))) (PreH27 : ((0 : Int) <= k)) (PreH28 : (k <= capacity_pre)) (PreH29 : ((0 : Int) <= pos)) (PreH30 : (pos <= capacity_pre)) (PreH31 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH32 : ((-1000000) <= current)) (PreH33 : (current <= 1000000)) (PreH34 : ((0 : Int) <= (current + (k * v)))) (PreH35 : ((current + (k * v)) <= 1000000)) (PreH36 : ((0 : Int) <= head)) (PreH37 : (head < tail)) (PreH38 : (tail <= (k + 1))) (PreH39 : (tail <= (capacity_pre + 1))) (PreH40 : (MKDPTableSafety weights_l i capacity_pre old_l)) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (MKDPValueBound old_l capacity_pre)) (PreH43 : (MKTransitionValueBound old_l w v cnt capacity_pre)) (PreH44 : (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre)) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre)) (PreH47 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre)) (PreH48 : (MKTransitionSafety old_l w cnt capacity_pre pos)) (PreH49 : (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH50 : ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v)))) (PreH51 : (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000)) (PreH52 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre)))) ,
  (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (k + 1)) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l i capacity_pre old_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (MKDPValueBound old_l capacity_pre) ” &&
  “ (MKTransitionValueBound old_l w v cnt capacity_pre) ” &&
  “ (MKItemResiduePrefixSafety old_l dp_l r w cnt k capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueResultSafety old_l qidx_l qval_l head tail r w (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKTransitionSafety old_l w cnt capacity_pre pos) ” &&
  “ (MKTransitionSemantics old_l w v cnt capacity_pre pos ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ ((0 : Int) <= ((Znth head qval_l (0 : Int)) + (k * v))) ” &&
  “ (((Znth head qval_l (0 : Int)) + (k * v)) <= 1000000) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l (0 : Int))) ∧ ((Znth idx weights_l (0 : Int)) <= (capacity_pre + 1))) ∧ ((0 : Int) <= (Znth idx values_l (0 : Int)))) ∧ ((Znth idx values_l (0 : Int)) <= 1000)) ∧ ((0 : Int) <= (Znth idx counts_l (0 : Int)))) ∧ ((Znth idx counts_l (0 : Int)) <= capacity_pre))) ”
  &&  (((dp_pre + (pos * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i dp_pre pos (0 : Int) (capacity_pre + 1) dp_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)

noncomputable def multipleKnapsack_partial_solve_wit_16 : Prop :=
  forall (q_val_pre : Int) (q_idx_pre : Int) (old_pre : Int) (dp_pre : Int) (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (dp_l : (List Int)) (old_l : (List Int)) (qidx_l : (List Int)) (qval_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH9 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH12 : (MKDPTableSafety weights_l n_pre capacity_pre dp_l)) (PreH13 : (MKDPTableSemantics weights_l values_l counts_l n_pre capacity_pre dp_l)) (PreH14 : (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l (0 : Int)))) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full dp_pre (capacity_pre + 1) dp_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ (MKDPTableSafety weights_l n_pre capacity_pre dp_l) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l n_pre capacity_pre dp_l) ” &&
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l (0 : Int))) ”
  &&  (((dp_pre + (capacity_pre * sizeof(INT)))) # Int |-> ((Znth capacity_pre dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre capacity_pre (0 : Int) (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full old_pre (capacity_pre + 1) old_l)
  ** (intArray.full q_idx_pre (capacity_pre + 1) qidx_l)
  ** (intArray.full q_val_pre (capacity_pre + 1) qval_l)


structure VC_Correct : Type where
  proof_of_multipleKnapsack_safety_wit_1 : multipleKnapsack_safety_wit_1
  proof_of_multipleKnapsack_safety_wit_2 : multipleKnapsack_safety_wit_2
  proof_of_multipleKnapsack_safety_wit_3 : multipleKnapsack_safety_wit_3
  proof_of_multipleKnapsack_safety_wit_4 : multipleKnapsack_safety_wit_4
  proof_of_multipleKnapsack_safety_wit_5 : multipleKnapsack_safety_wit_5
  proof_of_multipleKnapsack_safety_wit_6 : multipleKnapsack_safety_wit_6
  proof_of_multipleKnapsack_safety_wit_7 : multipleKnapsack_safety_wit_7
  proof_of_multipleKnapsack_safety_wit_8 : multipleKnapsack_safety_wit_8
  proof_of_multipleKnapsack_safety_wit_9 : multipleKnapsack_safety_wit_9
  proof_of_multipleKnapsack_safety_wit_10 : multipleKnapsack_safety_wit_10
  proof_of_multipleKnapsack_safety_wit_11 : multipleKnapsack_safety_wit_11
  proof_of_multipleKnapsack_safety_wit_13 : multipleKnapsack_safety_wit_13
  proof_of_multipleKnapsack_safety_wit_14 : multipleKnapsack_safety_wit_14
  proof_of_multipleKnapsack_safety_wit_15 : multipleKnapsack_safety_wit_15
  proof_of_multipleKnapsack_safety_wit_16 : multipleKnapsack_safety_wit_16
  proof_of_multipleKnapsack_safety_wit_17 : multipleKnapsack_safety_wit_17
  proof_of_multipleKnapsack_safety_wit_18 : multipleKnapsack_safety_wit_18
  proof_of_multipleKnapsack_safety_wit_19 : multipleKnapsack_safety_wit_19
  proof_of_multipleKnapsack_safety_wit_20 : multipleKnapsack_safety_wit_20
  proof_of_multipleKnapsack_safety_wit_21 : multipleKnapsack_safety_wit_21
  proof_of_multipleKnapsack_safety_wit_22 : multipleKnapsack_safety_wit_22
  proof_of_multipleKnapsack_safety_wit_23 : multipleKnapsack_safety_wit_23
  proof_of_multipleKnapsack_safety_wit_24 : multipleKnapsack_safety_wit_24
  proof_of_multipleKnapsack_safety_wit_25 : multipleKnapsack_safety_wit_25
  proof_of_multipleKnapsack_safety_wit_26 : multipleKnapsack_safety_wit_26
  proof_of_multipleKnapsack_return_wit_1 : multipleKnapsack_return_wit_1
  proof_of_multipleKnapsack_partial_solve_wit_1 : multipleKnapsack_partial_solve_wit_1
  proof_of_multipleKnapsack_partial_solve_wit_2 : multipleKnapsack_partial_solve_wit_2
  proof_of_multipleKnapsack_partial_solve_wit_3 : multipleKnapsack_partial_solve_wit_3
  proof_of_multipleKnapsack_partial_solve_wit_4 : multipleKnapsack_partial_solve_wit_4
  proof_of_multipleKnapsack_partial_solve_wit_5 : multipleKnapsack_partial_solve_wit_5
  proof_of_multipleKnapsack_partial_solve_wit_6 : multipleKnapsack_partial_solve_wit_6
  proof_of_multipleKnapsack_partial_solve_wit_7 : multipleKnapsack_partial_solve_wit_7
  proof_of_multipleKnapsack_partial_solve_wit_8 : multipleKnapsack_partial_solve_wit_8
  proof_of_multipleKnapsack_partial_solve_wit_9 : multipleKnapsack_partial_solve_wit_9
  proof_of_multipleKnapsack_partial_solve_wit_10 : multipleKnapsack_partial_solve_wit_10
  proof_of_multipleKnapsack_partial_solve_wit_11 : multipleKnapsack_partial_solve_wit_11
  proof_of_multipleKnapsack_partial_solve_wit_12 : multipleKnapsack_partial_solve_wit_12
  proof_of_multipleKnapsack_partial_solve_wit_13 : multipleKnapsack_partial_solve_wit_13
  proof_of_multipleKnapsack_partial_solve_wit_14 : multipleKnapsack_partial_solve_wit_14
  proof_of_multipleKnapsack_partial_solve_wit_15 : multipleKnapsack_partial_solve_wit_15
  proof_of_multipleKnapsack_partial_solve_wit_16 : multipleKnapsack_partial_solve_wit_16
  proof_of_multipleKnapsack_safety_wit_12 : multipleKnapsack_safety_wit_12
  proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1
  proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2
  proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3
  proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4
  proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5
  proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6
  proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7
  proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8
  proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9
  proof_of_multipleKnapsack_entail_wit_10 : multipleKnapsack_entail_wit_10
  proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11
  proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1
  proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2
  proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13
  proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14
  proof_of_multipleKnapsack_entail_wit_15_1 : multipleKnapsack_entail_wit_15_1
  proof_of_multipleKnapsack_entail_wit_15_2 : multipleKnapsack_entail_wit_15_2
  proof_of_multipleKnapsack_entail_wit_16 : multipleKnapsack_entail_wit_16
  proof_of_multipleKnapsack_entail_wit_17 : multipleKnapsack_entail_wit_17
  proof_of_multipleKnapsack_entail_wit_18 : multipleKnapsack_entail_wit_18
  proof_of_multipleKnapsack_entail_wit_19 : multipleKnapsack_entail_wit_19
  proof_of_multipleKnapsack_entail_wit_20 : multipleKnapsack_entail_wit_20
  proof_of_multipleKnapsack_entail_wit_21 : multipleKnapsack_entail_wit_21

end Algorithms.multiple_knapsack.lean.groundtruth.multiple_knapsack_goal
