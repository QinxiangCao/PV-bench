import SimpleC.SL.SeparationLogic

import Data_structures.binary_indexed_tree.lean.spec_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance binary_indexed_tree_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def lowbit_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ (x_pre ≠ (INT_MIN)) ”

noncomputable def lowbit_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre))) ” &&
  “ (1 <= (Z.land x_pre (-x_pre))) ” &&
  “ ((Z.land x_pre (-x_pre)) <= x_pre) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.land x_pre (-x_pre)) <= x_pre) ” &&
  “ (1 <= (Z.land x_pre (-x_pre))) ” &&
  “ ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre))) ”
  &&  emp
)

noncomputable def lowbit_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((Z.land x_pre (-x_pre)) <= x_pre)

noncomputable def lowbit_return_wit_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  (1 <= (Z.land x_pre (-x_pre)))

noncomputable def lowbit_return_wit_1_split_goal_3 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre)))

noncomputable def add_safety_wit_1 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (((Znth pos bit_cur (0 : Int)) + delta_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos bit_cur (0 : Int)) + delta_pre)) ”
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (((Znth pos bit_cur (0 : Int)) + delta_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos bit_cur (0 : Int)) + delta_pre)) ”
)

noncomputable def add_safety_wit_1_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (((Znth pos bit_cur (0 : Int)) + delta_pre) <= INT_MAX) ”

noncomputable def add_safety_wit_1_split_goal_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ ((INT_MIN) <= ((Znth pos bit_cur (0 : Int)) + delta_pre)) ”

noncomputable def add_safety_wit_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre))) (PreH11 : (FenwickRep a bit_l n_pre)) (PreH12 : (FenwickIntervalsIntSafe a n_pre)) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH14 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ ((pos + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + retval)) ”

noncomputable def add_entail_wit_1 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre)) (PreH6 : (FenwickIntervalsIntSafe a n_pre)) (PreH7 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_l)
|--
  EX bit_cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ (FenwickIntervalsIntSafe a n_pre) ” &&
  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos_pre delta_pre) ”
  &&  (intArray.full bit_pre (n_pre + 1) bit_cur)
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre)) (PreH6 : (FenwickIntervalsIntSafe a n_pre)) (PreH7 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) ,
  TT && emp 
|--
  “ (FenwickAddProgress bit_l bit_l n_pre pos_pre pos_pre delta_pre) ”
  &&  emp
)

noncomputable def add_entail_wit_1_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre)) (PreH6 : (FenwickIntervalsIntSafe a n_pre)) (PreH7 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) ,
  (FenwickAddProgress bit_l bit_l n_pre pos_pre pos_pre delta_pre)

noncomputable def add_entail_wit_2 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre))) (PreH11 : (FenwickRep a bit_l n_pre)) (PreH12 : (FenwickIntervalsIntSafe a n_pre)) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH14 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur_2 (0 : Int)) + delta_pre)) (bit_cur_2)))
|--
  EX bit_cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= (pos + retval)) ” &&
  “ ((pos + retval) <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ (FenwickIntervalsIntSafe a n_pre) ” &&
  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre (pos + retval) delta_pre) ”
  &&  (intArray.full bit_pre (n_pre + 1) bit_cur)
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre))) (PreH11 : (FenwickRep a bit_l n_pre)) (PreH12 : (FenwickIntervalsIntSafe a n_pre)) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH14 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  TT && emp 
|--
  “ (FenwickAddProgress bit_l (replace_Znth (pos) (((Znth pos bit_cur_2 (0 : Int)) + delta_pre)) (bit_cur_2)) n_pre pos_pre (pos + retval) delta_pre) ”
  &&  emp
)

noncomputable def add_entail_wit_2_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre))) (PreH11 : (FenwickRep a bit_l n_pre)) (PreH12 : (FenwickIntervalsIntSafe a n_pre)) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH14 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  (FenwickAddProgress bit_l (replace_Znth (pos) (((Znth pos bit_cur_2 (0 : Int)) + delta_pre)) (bit_cur_2)) n_pre pos_pre (pos + retval) delta_pre)

noncomputable def add_return_wit_1 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
|--
  EX bit_l1 : (List Int),
  “ (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_l1 n_pre) ” &&
  “ ((Znth ((0 : Int)) (bit_l1) ((0 : Int))) = (Znth ((0 : Int)) (bit_l) ((0 : Int)))) ”
  &&  (intArray.full bit_pre (n_pre + 1) bit_l1)
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  TT && emp 
|--
  “ ((Znth ((0 : Int)) (bit_cur) ((0 : Int))) = (Znth ((0 : Int)) (bit_l) ((0 : Int)))) ” &&
  “ (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_cur n_pre) ”
  &&  emp
)

noncomputable def add_return_wit_1_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  ((Znth ((0 : Int)) (bit_cur) ((0 : Int))) = (Znth ((0 : Int)) (bit_l) ((0 : Int))))

noncomputable def add_return_wit_1_split_goal_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_cur n_pre)

noncomputable def add_partial_solve_wit_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
|--
  “ (pos <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos) ” &&
  “ (pos <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ (FenwickIntervalsIntSafe a n_pre) ” &&
  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int |-> ((Znth pos bit_cur (0 : Int))))
  ** (intArray.missing_i bit_pre pos (0 : Int) (n_pre + 1) bit_cur)

noncomputable def add_partial_solve_wit_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
|--
  “ (pos <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos) ” &&
  “ (pos <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ (FenwickIntervalsIntSafe a n_pre) ” &&
  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i bit_pre pos (0 : Int) (n_pre + 1) bit_cur)

noncomputable def add_partial_solve_wit_3_pure : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ”

noncomputable def add_partial_solve_wit_3_aux : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : (FenwickIntervalsIntSafe a n_pre)) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre)) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (pos <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos) ” &&
  “ (pos <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ (FenwickIntervalsIntSafe a n_pre) ” &&
  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre) ”
  &&  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))

noncomputable def add_partial_solve_wit_3 : Prop := add_partial_solve_wit_3_pure -> add_partial_solve_wit_3_aux

noncomputable def query_safety_wit_1 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : (FenwickIntervalsIntSafe a n)) ,
  ((( &( "sum" ) )) # Int |->_)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos_pre))
  ** (intArray.full bit_pre (n + 1) bit_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def query_safety_wit_2 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos)) (PreH4 : (pos <= pos_pre)) (PreH5 : (pos_pre <= n)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (FenwickRep a bit_l n)) (PreH9 : (FenwickIntervalsIntSafe a n)) (PreH10 : (FenwickQueryState a pos_pre pos sum)) ,
  ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** (intArray.full bit_pre (n + 1) bit_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def query_safety_wit_3 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (sum + (Znth pos bit_l (0 : Int)))) ”
) \/
(
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (sum + (Znth pos bit_l (0 : Int)))) ”
)

noncomputable def query_safety_wit_3_split_goal_1 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ”

noncomputable def query_safety_wit_3_split_goal_2 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((INT_MIN) <= (sum + (Znth pos bit_l (0 : Int)))) ”

noncomputable def query_safety_wit_4 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > (0 : Int))) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : ((0 : Int) <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n)) (PreH13 : (FenwickIntervalsIntSafe a n)) (PreH14 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth pos bit_l (0 : Int)))))
|--
  “ ((pos - retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos - retval)) ”

noncomputable def query_entail_wit_1 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : (FenwickIntervalsIntSafe a n)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= pos_pre) ” &&
  “ (pos_pre <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= (0 : Int)) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ (FenwickIntervalsIntSafe a n) ” &&
  “ (FenwickQueryState a pos_pre pos_pre (0 : Int)) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)
) \/
(
forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : (FenwickIntervalsIntSafe a n)) ,
  TT && emp 
|--
  “ (FenwickQueryState a pos_pre pos_pre (0 : Int)) ”
  &&  emp
)

noncomputable def query_entail_wit_1_split_goal_1 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : (FenwickIntervalsIntSafe a n)) ,
  (FenwickQueryState a pos_pre pos_pre (0 : Int))

noncomputable def query_entail_wit_2 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > (0 : Int))) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : ((0 : Int) <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n)) (PreH13 : (FenwickIntervalsIntSafe a n)) (PreH14 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= (pos - retval)) ” &&
  “ ((pos - retval) <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= (sum + (Znth pos bit_l (0 : Int)))) ” &&
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ (FenwickIntervalsIntSafe a n) ” &&
  “ (FenwickQueryState a pos_pre (pos - retval) (sum + (Znth pos bit_l (0 : Int)))) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)
) \/
(
forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > (0 : Int))) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : ((0 : Int) <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n)) (PreH13 : (FenwickIntervalsIntSafe a n)) (PreH14 : (FenwickQueryState a pos_pre pos sum)) ,
  TT && emp 
|--
  “ (FenwickQueryState a pos_pre (pos - retval) (sum + (Znth pos bit_l (0 : Int)))) ” &&
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ (INT_MIN <= (sum + (Znth pos bit_l (0 : Int)))) ”
  &&  emp
)

noncomputable def query_entail_wit_2_split_goal_1 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > (0 : Int))) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : ((0 : Int) <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n)) (PreH13 : (FenwickIntervalsIntSafe a n)) (PreH14 : (FenwickQueryState a pos_pre pos sum)) ,
  (FenwickQueryState a pos_pre (pos - retval) (sum + (Znth pos bit_l (0 : Int))))

noncomputable def query_entail_wit_2_split_goal_2 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > (0 : Int))) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : ((0 : Int) <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n)) (PreH13 : (FenwickIntervalsIntSafe a n)) (PreH14 : (FenwickQueryState a pos_pre pos sum)) ,
  ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX)

noncomputable def query_entail_wit_2_split_goal_3 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > (0 : Int))) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : ((0 : Int) <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n)) (PreH13 : (FenwickIntervalsIntSafe a n)) (PreH14 : (FenwickQueryState a pos_pre pos sum)) ,
  (INT_MIN <= (sum + (Znth pos bit_l (0 : Int))))

noncomputable def query_return_wit_1 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos <= (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (sum = (FenwickPrefixSum (a) (pos_pre))) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)
) \/
(
forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos <= (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  TT && emp 
|--
  “ (sum = (FenwickPrefixSum (a) (pos_pre))) ”
  &&  emp
)

noncomputable def query_return_wit_1_split_goal_1 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos <= (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (sum = (FenwickPrefixSum (a) (pos_pre)))

noncomputable def query_partial_solve_wit_1 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (pos > (0 : Int)) ” &&
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= sum) ” &&
  “ (sum <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ (FenwickIntervalsIntSafe a n) ” &&
  “ (FenwickQueryState a pos_pre pos sum) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int |-> ((Znth pos bit_l (0 : Int))))
  ** (intArray.missing_i bit_pre pos (0 : Int) (n + 1) bit_l)

noncomputable def query_partial_solve_wit_2_pure : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth pos bit_l (0 : Int)))))
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ”

noncomputable def query_partial_solve_wit_2_aux : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : (FenwickIntervalsIntSafe a n)) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (pos > (0 : Int)) ” &&
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= sum) ” &&
  “ (sum <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ (FenwickIntervalsIntSafe a n) ” &&
  “ (FenwickQueryState a pos_pre pos sum) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)

noncomputable def query_partial_solve_wit_2 : Prop := query_partial_solve_wit_2_pure -> query_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_lowbit_safety_wit_1 : lowbit_safety_wit_1
  proof_of_add_safety_wit_2 : add_safety_wit_2
  proof_of_add_partial_solve_wit_1 : add_partial_solve_wit_1
  proof_of_add_partial_solve_wit_2 : add_partial_solve_wit_2
  proof_of_add_partial_solve_wit_3_pure : add_partial_solve_wit_3_pure
  proof_of_add_partial_solve_wit_3 : add_partial_solve_wit_3
  proof_of_query_safety_wit_1 : query_safety_wit_1
  proof_of_query_safety_wit_2 : query_safety_wit_2
  proof_of_query_safety_wit_4 : query_safety_wit_4
  proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1
  proof_of_query_partial_solve_wit_2_pure : query_partial_solve_wit_2_pure
  proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2
  proof_of_lowbit_return_wit_1 : lowbit_return_wit_1
  proof_of_add_safety_wit_1 : add_safety_wit_1
  proof_of_add_entail_wit_1 : add_entail_wit_1
  proof_of_add_entail_wit_2 : add_entail_wit_2
  proof_of_add_return_wit_1 : add_return_wit_1
  proof_of_query_safety_wit_3 : query_safety_wit_3
  proof_of_query_entail_wit_1 : query_entail_wit_1
  proof_of_query_entail_wit_2 : query_entail_wit_2
  proof_of_query_return_wit_1 : query_return_wit_1

end Data_structures.binary_indexed_tree.lean.groundtruth.binary_indexed_tree_goal
