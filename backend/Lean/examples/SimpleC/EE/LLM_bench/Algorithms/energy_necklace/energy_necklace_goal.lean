import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
open SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance energy_necklace_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def energyNecklace_safety_wit_1 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : (EnergyLabelsBounded beads_l n_pre)) (PreH5 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "total" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full vals_pre (2 * n_pre))
  ** (intArray.undef_full dp_pre ((2 * n_pre) * (2 * n_pre)))
|--
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * n_pre)) ”

noncomputable def energyNecklace_safety_wit_2 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : (EnergyLabelsBounded beads_l n_pre)) (PreH5 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "total" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full vals_pre (2 * n_pre))
  ** (intArray.undef_full dp_pre ((2 * n_pre) * (2 * n_pre)))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def energyNecklace_safety_wit_3 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre)) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full vals_pre total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_4 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) (i + 1) (vals_l ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg vals_pre (i + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def energyNecklace_safety_wit_5 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (vals_l)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH10 : (EnergyLabelsBounded beads_l n_pre)) (PreH11 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) n_pre vals_l)
  ** (intArray.undef_seg vals_pre n_pre total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_6 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg vals_pre (n_pre + i) total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ ((n_pre + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + i)) ”

noncomputable def energyNecklace_safety_wit_7 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) ((n_pre + i) + 1) (vals_l ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg vals_pre ((n_pre + i) + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def energyNecklace_safety_wit_8 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH9 : (EnergyLabelsBounded beads_l n_pre)) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_9 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (total * width))) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l (0 : Int)) = (0 : Int)))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.seg dp_pre (0 : Int) i dp_l)
  ** (intArray.undef_seg dp_pre i (total * width))
|--
  “ ((total * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total * width)) ”

noncomputable def energyNecklace_safety_wit_10 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.seg dp_pre (0 : Int) i dp_l)
  ** (intArray.undef_seg dp_pre i (total * width))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_11 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg dp_pre (0 : Int) (i + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (i + 1) (total * width))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def energyNecklace_safety_wit_12 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (total * width))) (PreH9 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH10 : (EnergyZeroTable dp_l total width)) (PreH11 : (EnergyLenDone vals_l dp_l total width 2)) (PreH12 : (EnergyLabelsBounded beads_l n_pre)) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def energyNecklace_safety_wit_13 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH13 : (EnergyLenDone vals_l dp_l total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_14 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left <= (total - len))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLeftProgress vals_l dp_l total width len left)) (PreH15 : (EnergyLabelsBounded beads_l n_pre)) (PreH16 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((total - len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total - len)) ”

noncomputable def energyNecklace_safety_wit_15 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (((left + len) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + len) - 1)) ”

noncomputable def energyNecklace_safety_wit_16 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((left + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + len)) ”

noncomputable def energyNecklace_safety_wit_17 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_18 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_19 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (((left * width) + split) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * width) + split)) ”

noncomputable def energyNecklace_safety_wit_20 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((left * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * width)) ”

noncomputable def energyNecklace_safety_wit_21 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
|--
  “ ((((split + 1) * width) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((split + 1) * width) + right)) ”

noncomputable def energyNecklace_safety_wit_22 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
|--
  “ (((split + 1) * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((split + 1) * width)) ”

noncomputable def energyNecklace_safety_wit_23 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def energyNecklace_safety_wit_24 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_25 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ”
) \/
(
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ”
)

noncomputable def energyNecklace_safety_wit_25_split_goal_1 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_25_split_goal_2 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((INT_MIN) <= (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ”

noncomputable def energyNecklace_safety_wit_26 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((right + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right + 1)) ”

noncomputable def energyNecklace_safety_wit_27 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int)))) ”
) \/
(
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int)))) ”
)

noncomputable def energyNecklace_safety_wit_27_split_goal_1 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_27_split_goal_2 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((INT_MIN) <= ((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int)))) ”

noncomputable def energyNecklace_safety_wit_28 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def energyNecklace_safety_wit_29 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_30 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_31 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ”
) \/
(
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ”
)

noncomputable def energyNecklace_safety_wit_31_split_goal_1 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_31_split_goal_2 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((INT_MIN) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ”

noncomputable def energyNecklace_safety_wit_32 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) ”
) \/
(
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) ”
)

noncomputable def energyNecklace_safety_wit_32_split_goal_1 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_32_split_goal_2 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full vals_pre total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full dp_pre (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((INT_MIN) <= ((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) ”

noncomputable def energyNecklace_safety_wit_33 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1) < total)) (PreH15 : (left_value = (Znth ((left * width) + split) dp_l (0 : Int)))) (PreH16 : (right_value = (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) (PreH17 : (gain = (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) (PreH18 : (candidate = ((left_value + right_value) + gain))) (PreH19 : ((0 : Int) <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l)) = (total * width))) (PreH25 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH26 : (EnergySplitProgress vals_l dp_l total width len left (split + 1) best)) (PreH27 : (EnergyLabelsBounded beads_l n_pre)) (PreH28 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def energyNecklace_safety_wit_34 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH20 : (EnergySplitProgress vals_l dp_l total width len left right best)) (PreH21 : (EnergyIntervalBest vals_l left right best)) (PreH22 : (EnergyLabelsBounded beads_l n_pre)) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (((left * width) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * width) + right)) ”

noncomputable def energyNecklace_safety_wit_35 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH20 : (EnergySplitProgress vals_l dp_l total width len left right best)) (PreH21 : (EnergyIntervalBest vals_l left right best)) (PreH22 : (EnergyLabelsBounded beads_l n_pre)) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((left * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * width)) ”

noncomputable def energyNecklace_safety_wit_36 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_old : (List Int)) (dp_new : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((0 : Int) <= best)) (PreH13 : (best <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_old)) = (total * width))) (PreH16 : ((Zlength (dp_new)) = (total * width))) (PreH17 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH18 : (EnergyUpdatedCell vals_l dp_old dp_new width left right best)) (PreH19 : (EnergyLeftProgress vals_l dp_new total width len (left + 1))) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_new)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def energyNecklace_safety_wit_37 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (total * width))) (PreH11 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH12 : (EnergyLenDone vals_l dp_l total width (len + 1))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((len + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len + 1)) ”

noncomputable def energyNecklace_safety_wit_38 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH13 : (EnergyLenDone vals_l dp_l total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_39 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (total * width))) (PreH9 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH10 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH11 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (0 : Int) answer)) (PreH12 : (EnergyLabelsBounded beads_l n_pre)) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "start" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_40 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (((((start * width) + start) + n_pre) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((start * width) + start) + n_pre) - 1)) ”

noncomputable def energyNecklace_safety_wit_41 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((((start * width) + start) + n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((start * width) + start) + n_pre)) ”

noncomputable def energyNecklace_safety_wit_42 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (((start * width) + start) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((start * width) + start)) ”

noncomputable def energyNecklace_safety_wit_43 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((start * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start * width)) ”

noncomputable def energyNecklace_safety_wit_44 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_45 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH10 : ((0 : Int) <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l)) = (total * width))) (PreH16 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH17 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH18 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) value)) (PreH19 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1) answer)) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "vals" ) )) # Ptr |-> (vals_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ ((start + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start + 1)) ”

noncomputable def energyNecklace_entail_wit_1 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : (EnergyLabelsBounded beads_l n_pre)) (PreH5 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full vals_pre (2 * n_pre))
  ** (intArray.undef_full dp_pre ((2 * n_pre) * (2 * n_pre)))
|--
  “ ((2 * n_pre) = (2 * n_pre)) ” &&
  “ ((2 * n_pre) = (2 * n_pre)) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= (2 * n_pre)) ” &&
  “ ((2 * n_pre) <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full vals_pre (2 * n_pre))
  ** (intArray.undef_full dp_pre ((2 * n_pre) * (2 * n_pre)))

noncomputable def energyNecklace_entail_wit_2 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre)) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full vals_pre total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (0 : Int) vals_l)
  ** (intArray.undef_seg vals_pre (0 : Int) total)
  ** (intArray.undef_full dp_pre (total * width))
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre)) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre)) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = (Znth k beads_l (0 : Int))))

noncomputable def energyNecklace_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre)) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def energyNecklace_entail_wit_3 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l_2 (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) (i + 1) (vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg vals_pre (i + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full dp_pre (total * width))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (i + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (i + 1))) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (i + 1) vals_l)
  ** (intArray.undef_seg vals_pre (i + 1) total)
  ** (intArray.undef_full dp_pre (total * width))
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l_2 (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ ((Zlength ((vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l_2 (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((Zlength ((vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))) = (i + 1))

noncomputable def energyNecklace_entail_wit_4 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth k_2 vals_l_2 (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) i vals_l_2)
  ** (intArray.undef_seg vals_pre i total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) n_pre vals_l)
  ** (intArray.undef_seg vals_pre n_pre total)
  ** (intArray.undef_full dp_pre (total * width))
) \/
(
forall (vals_pre : Int) (n_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth k_2 vals_l_2 (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) i vals_l_2)
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.seg vals_pre (0 : Int) n_pre vals_l)
)

noncomputable def energyNecklace_entail_wit_5 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (vals_l_2)) = n_pre)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth k_3 vals_l_2 (0 : Int)) = (Znth k_3 beads_l (0 : Int))))) (PreH10 : (EnergyLabelsBounded beads_l n_pre)) (PreH11 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) n_pre vals_l_2)
  ** (intArray.undef_seg vals_pre n_pre total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (0 : Int))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (0 : Int))) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + (0 : Int)) vals_l)
  ** (intArray.undef_seg vals_pre (n_pre + (0 : Int)) total)
  ** (intArray.undef_full dp_pre (total * width))
) \/
(
forall (vals_pre : Int) (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (vals_l_2)) = n_pre)) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth k_3 vals_l_2 (0 : Int)) = (Znth k_3 beads_l (0 : Int))))) (PreH10 : (EnergyLabelsBounded beads_l n_pre)) (PreH11 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) n_pre vals_l_2)
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (0 : Int))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (0 : Int))) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.seg vals_pre (0 : Int) (n_pre + (0 : Int)) vals_l)
)

noncomputable def energyNecklace_entail_wit_6 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l_2 (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l_2 (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) ((n_pre + i) + 1) (vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg vals_pre ((n_pre + i) + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full dp_pre (total * width))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (i + 1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + (i + 1)) vals_l)
  ** (intArray.undef_seg vals_pre (n_pre + (i + 1)) total)
  ** (intArray.undef_full dp_pre (total * width))
) \/
(
forall (vals_pre : Int) (n_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l_2 (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l_2 (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) ((n_pre + i) + 1) (vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (i + 1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.seg vals_pre (0 : Int) (n_pre + (i + 1)) vals_l)
)

noncomputable def energyNecklace_entail_wit_7 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l_2 (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l_2 (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + i) vals_l_2)
  ** (intArray.undef_seg vals_pre (n_pre + i) total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.undef_full dp_pre (total * width))
) \/
(
forall (vals_pre : Int) (n_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l_2 (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l_2 (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg vals_pre (0 : Int) (n_pre + i) vals_l_2)
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full vals_pre total vals_l)
)

noncomputable def energyNecklace_entail_wit_8 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH9 : (EnergyLabelsBounded beads_l n_pre)) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.undef_full dp_pre (total * width))
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (total * width)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k dp_l (0 : Int)) = (0 : Int))) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.seg dp_pre (0 : Int) (0 : Int) dp_l)
  ** (intArray.undef_seg dp_pre (0 : Int) (total * width))
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH9 : (EnergyLabelsBounded beads_l n_pre)) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = (0 : Int))) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH9 : (EnergyLabelsBounded beads_l n_pre)) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = (0 : Int)))

noncomputable def energyNecklace_entail_wit_8_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH9 : (EnergyLabelsBounded beads_l n_pre)) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def energyNecklace_entail_wit_9 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l_2 (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg dp_pre (0 : Int) (i + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (i + 1) (total * width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (i + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (total * width)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (i + 1))) -> ((Znth k dp_l (0 : Int)) = (0 : Int))) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.seg dp_pre (0 : Int) (i + 1) dp_l)
  ** (intArray.undef_seg dp_pre (i + 1) (total * width))
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l_2 (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l_2 (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1))

noncomputable def energyNecklace_entail_wit_10 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l_2 (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.seg dp_pre (0 : Int) i dp_l_2)
  ** (intArray.undef_seg dp_pre i (total * width))
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyZeroTable dp_l total width) ” &&
  “ (EnergyLenDone vals_l dp_l total width 2) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (dp_pre : Int) (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l_2 (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.seg dp_pre (0 : Int) i dp_l_2)
|--
  EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre) ” &&
  “ (EnergyZeroTable dp_l total width) ” &&
  “ (EnergyLenDone vals_l_2 dp_l total width 2) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full dp_pre (total * width) dp_l)
)

noncomputable def energyNecklace_entail_wit_11 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH10 : (EnergyZeroTable dp_l_2 total width)) (PreH11 : (EnergyLenDone vals_l_2 dp_l_2 total width 2)) (PreH12 : (EnergyLabelsBounded beads_l n_pre)) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width 2) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)

noncomputable def energyNecklace_entail_wit_12 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (total - len)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLeftProgress vals_l dp_l total width len (0 : Int)) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyLeftProgress vals_l_2 dp_l_2 (2 * n_pre) width len (0 : Int)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_12_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyLeftProgress vals_l_2 dp_l_2 (2 * n_pre) width len (0 : Int))

noncomputable def energyNecklace_entail_wit_13 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (((left + len) - 1) = ((left + len) - 1)) ” &&
  “ (left < ((left + len) - 1)) ” &&
  “ ((0 : Int) <= ((left + len) - 1)) ” &&
  “ (((left + len) - 1) < total) ” &&
  “ ((((left + len) - 1) + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left left (0 : Int)) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) width len left left (0 : Int)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_13_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) width len left left (0 : Int))

noncomputable def energyNecklace_entail_wit_14 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left < right)) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best)) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ (left <= left) ” &&
  “ (left <= right) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left left best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left < right)) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best)) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (best <= 2100000000) ” &&
  “ ((0 : Int) <= best) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_14_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left < right)) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best)) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (best <= 2100000000)

noncomputable def energyNecklace_entail_wit_14_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left < right)) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best)) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((0 : Int) <= best)

noncomputable def energyNecklace_entail_wit_15 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left split best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ ((((split + 1) * width) + ((left + len) - 1)) < ((2 * n_pre) * width)) ” &&
  “ (((left * width) + split) < ((2 * n_pre) * width)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_15_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((((split + 1) * width) + ((left + len) - 1)) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_15_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (((left * width) + split) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_16 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
|--
  EX vals_l_2 : (List Int), EX dp_l_2 : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Znth ((left * width) + split) dp_l (0 : Int)) = (Znth ((left * width) + split) dp_l_2 (0 : Int))) ” &&
  “ ((Znth (((split + 1) * width) + right) dp_l (0 : Int)) = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int))) ” &&
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int)))) ” &&
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) = (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ” &&
  “ ((0 : Int) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ” &&
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l_2)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre) ” &&
  “ (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ ((((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int)))) <= 2100000000) ” &&
  “ ((0 : Int) <= (((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int))))) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_16_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int)))) <= 2100000000)

noncomputable def energyNecklace_entail_wit_16_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((0 : Int) <= (((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int)))))

noncomputable def energyNecklace_entail_wit_17_1 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH28 : (EnergyLabelsBounded beads_l n_pre)) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((right + 1) < total) ” &&
  “ (left_value = (Znth ((left * width) + split) dp_l (0 : Int))) ” &&
  “ (right_value = (Znth (((split + 1) * width) + right) dp_l (0 : Int))) ” &&
  “ (gain = (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ” &&
  “ (candidate = ((left_value + right_value) + gain)) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 2100000000) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left (split + 1) candidate) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH28 : (EnergyLabelsBounded beads_l n_pre)) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) total len left (split + 1) ((left_value + right_value) + gain)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_17_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH28 : (EnergyLabelsBounded beads_l n_pre)) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) total len left (split + 1) ((left_value + right_value) + gain))

noncomputable def energyNecklace_entail_wit_17_2 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH28 : (EnergyLabelsBounded beads_l n_pre)) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((right + 1) < total) ” &&
  “ (left_value = (Znth ((left * width) + split) dp_l (0 : Int))) ” &&
  “ (right_value = (Znth (((split + 1) * width) + right) dp_l (0 : Int))) ” &&
  “ (gain = (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ” &&
  “ (candidate = ((left_value + right_value) + gain)) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 2100000000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left (split + 1) best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH28 : (EnergyLabelsBounded beads_l n_pre)) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) total len left (split + 1) best) ” &&
  “ (best <= 2100000000) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_17_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH28 : (EnergyLabelsBounded beads_l n_pre)) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) total len left (split + 1) best)

noncomputable def energyNecklace_entail_wit_17_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH28 : (EnergyLabelsBounded beads_l n_pre)) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (best <= 2100000000)

noncomputable def energyNecklace_entail_wit_18 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1) < total)) (PreH15 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH16 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH17 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH18 : (candidate = ((left_value + right_value) + gain))) (PreH19 : ((0 : Int) <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH26 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left (split + 1) best)) (PreH27 : (EnergyLabelsBounded beads_l n_pre)) (PreH28 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left (split + 1) best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)

noncomputable def energyNecklace_entail_wit_19 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + right)) ” &&
  “ (((left * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left right best) ” &&
  “ (EnergyIntervalBest vals_l left right best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyIntervalBest vals_l_2 left ((left + len) - 1) best) ” &&
  “ (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) width len left ((left + len) - 1) best) ” &&
  “ (((left * width) + ((left + len) - 1)) < ((2 * n_pre) * width)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_19_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyIntervalBest vals_l_2 left ((left + len) - 1) best)

noncomputable def energyNecklace_entail_wit_19_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergySplitProgress vals_l_2 dp_l_2 (2 * n_pre) width len left ((left + len) - 1) best)

noncomputable def energyNecklace_entail_wit_19_split_goal_3 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best)) (PreH25 : (EnergyLabelsBounded beads_l n_pre)) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (((left * width) + ((left + len) - 1)) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_20 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : (EnergySplitProgress vals_l_2 dp_l total width len left right best)) (PreH21 : (EnergyIntervalBest vals_l_2 left right best)) (PreH22 : (EnergyLabelsBounded beads_l n_pre)) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full dp_pre (total * width) (replace_Znth (((left * width) + right)) (best) (dp_l)))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
|--
  EX vals_l : (List Int), EX dp_new : (List Int), EX dp_old : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_old)) = (total * width)) ” &&
  “ ((Zlength (dp_new)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyUpdatedCell vals_l dp_old dp_new width left right best) ” &&
  “ (EnergyLeftProgress vals_l dp_new total width len (left + 1)) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_new)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : (EnergySplitProgress vals_l_2 dp_l total width len left right best)) (PreH21 : (EnergyIntervalBest vals_l_2 left right best)) (PreH22 : (EnergyLabelsBounded beads_l n_pre)) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  EX dp_old : (List Int),
  “ ((Zlength (dp_old)) = ((2 * (Zlength (beads_l))) * total)) ” &&
  “ ((Zlength ((replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l)))) = ((2 * (Zlength (beads_l))) * total)) ” &&
  “ (EnergyUpdatedCell vals_l_2 dp_old (replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l)) total left ((left + len) - 1) best) ” &&
  “ (EnergyLeftProgress vals_l_2 (replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l)) (2 * (Zlength (beads_l))) total len (left + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_21 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_old : (List Int)) (dp_new : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((0 : Int) <= best)) (PreH13 : (best <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_old)) = (total * width))) (PreH16 : ((Zlength (dp_new)) = (total * width))) (PreH17 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH18 : (EnergyUpdatedCell vals_l_2 dp_old dp_new width left right best)) (PreH19 : (EnergyLeftProgress vals_l_2 dp_new total width len (left + 1))) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_new)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= (total - len)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLeftProgress vals_l dp_l total width len (left + 1)) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)

noncomputable def energyNecklace_entail_wit_22 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (len + 1)) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyLenDone vals_l_2 dp_l_2 (2 * n_pre) width (len + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_22_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left)) (PreH16 : (EnergyLabelsBounded beads_l n_pre)) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyLenDone vals_l_2 dp_l_2 (2 * n_pre) width (len + 1))

noncomputable def energyNecklace_entail_wit_23 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (total * width))) (PreH11 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH12 : (EnergyLenDone vals_l_2 dp_l_2 total width (len + 1))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= (len + 1)) ” &&
  “ ((len + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (len + 1)) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)

noncomputable def energyNecklace_entail_wit_24 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (0 : Int) (0 : Int)) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre (2 * n_pre) width (0 : Int) (0 : Int)) ” &&
  “ (EnergyLenDone vals_l_2 dp_l_2 (2 * n_pre) width (n_pre + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_24_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre (2 * n_pre) width (0 : Int) (0 : Int))

noncomputable def energyNecklace_entail_wit_24_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyLenDone vals_l_2 dp_l_2 (2 * n_pre) width (n_pre + 1))

noncomputable def energyNecklace_entail_wit_25 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (0 : Int) answer)) (PreH12 : (EnergyLabelsBounded beads_l n_pre)) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (0 : Int) answer) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (0 : Int) answer)) (PreH12 : (EnergyLabelsBounded beads_l n_pre)) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (answer <= 2100000000) ” &&
  “ ((0 : Int) <= answer) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_25_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (0 : Int) answer)) (PreH12 : (EnergyLabelsBounded beads_l n_pre)) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (answer <= 2100000000)

noncomputable def energyNecklace_entail_wit_25_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (0 : Int) answer)) (PreH12 : (EnergyLabelsBounded beads_l n_pre)) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((0 : Int) <= answer)

noncomputable def energyNecklace_entail_wit_26 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ ((0 : Int) <= ((((start * width) + start) + n_pre) - 1)) ” &&
  “ (((((start * width) + start) + n_pre) - 1) < (total * width)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int))) ” &&
  “ (((((start * width) + start) + n_pre) - 1) < ((2 * n_pre) * width)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_26_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))

noncomputable def energyNecklace_entail_wit_26_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (((((start * width) + start) + n_pre) - 1) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_27 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
|--
  EX vals_l : (List Int), EX dp_l_2 : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ ((Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)) = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)) <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l_2)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l_2 total width (n_pre + 1)) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l_2 n_pre total width start answer) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l_2)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ ((Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int)) <= 2100000000) ” &&
  “ ((0 : Int) <= (Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int))) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_27_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int)) <= 2100000000)

noncomputable def energyNecklace_entail_wit_27_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  ((0 : Int) <= (Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int)))

noncomputable def energyNecklace_entail_wit_28_1 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyLabelsBounded beads_l n_pre)) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 2100000000) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) value) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1) value) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyLabelsBounded beads_l n_pre)) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre (2 * n_pre) total (start + 1) value) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_28_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyLabelsBounded beads_l n_pre)) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre (2 * n_pre) total (start + 1) value)

noncomputable def energyNecklace_entail_wit_28_2 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyLabelsBounded beads_l n_pre)) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 2100000000) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) value) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1) answer) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyLabelsBounded beads_l n_pre)) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre (2 * n_pre) total (start + 1) answer) ” &&
  “ (answer <= 2100000000) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_28_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyLabelsBounded beads_l n_pre)) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre (2 * n_pre) total (start + 1) answer)

noncomputable def energyNecklace_entail_wit_28_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyLabelsBounded beads_l n_pre)) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (answer <= 2100000000)

noncomputable def energyNecklace_entail_wit_29 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH10 : ((0 : Int) <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH17 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH19 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (start + 1) answer)) (PreH20 : (EnergyLabelsBounded beads_l n_pre)) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= (start + 1)) ” &&
  “ ((start + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1) answer) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)

noncomputable def energyNecklace_entail_wit_30 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyNecklaceAnswer beads_l n_pre answer) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
) \/
(
forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  TT && emp 
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_30_split_goal_1 : Prop :=
  forall (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer)) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (EnergyNecklaceAnswer beads_l n_pre answer)

noncomputable def energyNecklace_return_wit_1 : Prop :=
  (
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer <= 2100000000)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (total * width))) (PreH11 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH12 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH13 : (EnergyNecklaceAnswer beads_l n_pre answer)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX dp_l : (List Int), EX vals_l : (List Int),
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l (2 * n_pre) (2 * n_pre) (n_pre + 1)) ” &&
  “ (EnergyNecklaceAnswer beads_l n_pre answer) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre (2 * n_pre) vals_l)
  ** (intArray.full dp_pre ((2 * n_pre) * (2 * n_pre)) dp_l)
) \/
(
forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_l : (List Int)) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer <= 2100000000)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (total * width))) (PreH11 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH12 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1))) (PreH13 : (EnergyNecklaceAnswer beads_l n_pre answer)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l_2)
  ** (intArray.full dp_pre (total * width) dp_l_2)
|--
  EX dp_l : (List Int), EX vals_l : (List Int),
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l (2 * n_pre) (2 * n_pre) (n_pre + 1)) ” &&
  “ (EnergyNecklaceAnswer beads_l n_pre answer) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ”
  &&  (intArray.full vals_pre (2 * n_pre) vals_l)
  ** (intArray.full dp_pre ((2 * n_pre) * (2 * n_pre)) dp_l)
)

noncomputable def energyNecklace_partial_solve_wit_1 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) i vals_l)
  ** (intArray.undef_seg vals_pre i total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int |-> ((Znth i beads_l (0 : Int))))
  ** (intArray.missing_i beads_pre i (0 : Int) n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) i vals_l)
  ** (intArray.undef_seg vals_pre i total)
  ** (intArray.undef_full dp_pre (total * width))

noncomputable def energyNecklace_partial_solve_wit_2 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : (EnergyLabelsBounded beads_l n_pre)) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) i vals_l)
  ** (intArray.undef_seg vals_pre i total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((vals_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg vals_pre (i + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) i vals_l)
  ** (intArray.undef_full dp_pre (total * width))

noncomputable def energyNecklace_partial_solve_wit_3 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg vals_pre (n_pre + i) total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + i)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int |-> ((Znth i beads_l (0 : Int))))
  ** (intArray.missing_i beads_pre i (0 : Int) n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg vals_pre (n_pre + i) total)
  ** (intArray.undef_full dp_pre (total * width))

noncomputable def energyNecklace_partial_solve_wit_4 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int))))) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int))))) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg vals_pre (n_pre + i) total)
  ** (intArray.undef_full dp_pre (total * width))
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + i)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k vals_l (0 : Int)) = (Znth k beads_l (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((Znth (n_pre + k_2) vals_l (0 : Int)) = (Znth k_2 beads_l (0 : Int)))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((vals_pre + ((n_pre + i) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg vals_pre ((n_pre + i) + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg vals_pre (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_full dp_pre (total * width))

noncomputable def energyNecklace_partial_solve_wit_5 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l (0 : Int)) = (0 : Int)))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLabelsBounded beads_l n_pre)) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.seg dp_pre (0 : Int) i dp_l)
  ** (intArray.undef_seg dp_pre i (total * width))
|--
  “ (i < (total * width)) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (total * width)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k dp_l (0 : Int)) = (0 : Int))) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (i + 1) (total * width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.seg dp_pre (0 : Int) i dp_l)

noncomputable def energyNecklace_partial_solve_wit_6 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left split best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((dp_pre + (((left * width) + split) * sizeof(INT)))) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre ((left * width) + split) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)

noncomputable def energyNecklace_partial_solve_wit_7 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left split best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((dp_pre + ((((split + 1) * width) + right) * sizeof(INT)))) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre (((split + 1) * width) + right) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)

noncomputable def energyNecklace_partial_solve_wit_8 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left split best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((vals_pre + (left * sizeof(INT)))) # Int |-> ((Znth left vals_l (0 : Int))))
  ** (intArray.missing_i vals_pre left (0 : Int) total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)

noncomputable def energyNecklace_partial_solve_wit_9 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left split best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((vals_pre + ((split + 1) * sizeof(INT)))) # Int |-> ((Znth (split + 1) vals_l (0 : Int))))
  ** (intArray.missing_i vals_pre (split + 1) (0 : Int) total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)

noncomputable def energyNecklace_partial_solve_wit_10 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best)) (PreH31 : (EnergyLabelsBounded beads_l n_pre)) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left split best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((vals_pre + ((right + 1) * sizeof(INT)))) # Int |-> ((Znth (right + 1) vals_l (0 : Int))))
  ** (intArray.missing_i vals_pre (right + 1) (0 : Int) total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)

noncomputable def energyNecklace_partial_solve_wit_11 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH20 : (EnergySplitProgress vals_l dp_l total width len left right best)) (PreH21 : (EnergyIntervalBest vals_l left right best)) (PreH22 : (EnergyLabelsBounded beads_l n_pre)) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + right)) ” &&
  “ (((left * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergySplitProgress vals_l dp_l total width len left right best) ” &&
  “ (EnergyIntervalBest vals_l left right best) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((dp_pre + (((left * width) + right) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i dp_pre ((left * width) + right) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)

noncomputable def energyNecklace_partial_solve_wit_12 : Prop :=
  forall (dp_pre : Int) (vals_pre : Int) (n_pre : Int) (beads_pre : Int) (beads_l : (List Int)) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1))) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer)) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH17 : (EnergyLabelsBounded beads_l n_pre)) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000)) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)
  ** (intArray.full dp_pre (total * width) dp_l)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ ((0 : Int) <= ((((start * width) + start) + n_pre) - 1)) ” &&
  “ (((((start * width) + start) + n_pre) - 1) < (total * width)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1)) ” &&
  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ (EnergyLabelsBounded beads_l n_pre) ” &&
  “ (EnergyComputationBounded beads_l n_pre 2100000000) ”
  &&  (((dp_pre + (((((start * width) + start) + n_pre) - 1) * sizeof(INT)))) # Int |-> ((Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre ((((start * width) + start) + n_pre) - 1) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full vals_pre total vals_l)


structure VC_Correct : Type where
  proof_of_energyNecklace_safety_wit_1 : energyNecklace_safety_wit_1
  proof_of_energyNecklace_safety_wit_2 : energyNecklace_safety_wit_2
  proof_of_energyNecklace_safety_wit_3 : energyNecklace_safety_wit_3
  proof_of_energyNecklace_safety_wit_4 : energyNecklace_safety_wit_4
  proof_of_energyNecklace_safety_wit_5 : energyNecklace_safety_wit_5
  proof_of_energyNecklace_safety_wit_6 : energyNecklace_safety_wit_6
  proof_of_energyNecklace_safety_wit_7 : energyNecklace_safety_wit_7
  proof_of_energyNecklace_safety_wit_8 : energyNecklace_safety_wit_8
  proof_of_energyNecklace_safety_wit_9 : energyNecklace_safety_wit_9
  proof_of_energyNecklace_safety_wit_10 : energyNecklace_safety_wit_10
  proof_of_energyNecklace_safety_wit_11 : energyNecklace_safety_wit_11
  proof_of_energyNecklace_safety_wit_12 : energyNecklace_safety_wit_12
  proof_of_energyNecklace_safety_wit_13 : energyNecklace_safety_wit_13
  proof_of_energyNecklace_safety_wit_14 : energyNecklace_safety_wit_14
  proof_of_energyNecklace_safety_wit_15 : energyNecklace_safety_wit_15
  proof_of_energyNecklace_safety_wit_16 : energyNecklace_safety_wit_16
  proof_of_energyNecklace_safety_wit_17 : energyNecklace_safety_wit_17
  proof_of_energyNecklace_safety_wit_18 : energyNecklace_safety_wit_18
  proof_of_energyNecklace_safety_wit_19 : energyNecklace_safety_wit_19
  proof_of_energyNecklace_safety_wit_20 : energyNecklace_safety_wit_20
  proof_of_energyNecklace_safety_wit_21 : energyNecklace_safety_wit_21
  proof_of_energyNecklace_safety_wit_22 : energyNecklace_safety_wit_22
  proof_of_energyNecklace_safety_wit_23 : energyNecklace_safety_wit_23
  proof_of_energyNecklace_safety_wit_24 : energyNecklace_safety_wit_24
  proof_of_energyNecklace_safety_wit_26 : energyNecklace_safety_wit_26
  proof_of_energyNecklace_safety_wit_28 : energyNecklace_safety_wit_28
  proof_of_energyNecklace_safety_wit_29 : energyNecklace_safety_wit_29
  proof_of_energyNecklace_safety_wit_30 : energyNecklace_safety_wit_30
  proof_of_energyNecklace_safety_wit_33 : energyNecklace_safety_wit_33
  proof_of_energyNecklace_safety_wit_34 : energyNecklace_safety_wit_34
  proof_of_energyNecklace_safety_wit_35 : energyNecklace_safety_wit_35
  proof_of_energyNecklace_safety_wit_36 : energyNecklace_safety_wit_36
  proof_of_energyNecklace_safety_wit_37 : energyNecklace_safety_wit_37
  proof_of_energyNecklace_safety_wit_38 : energyNecklace_safety_wit_38
  proof_of_energyNecklace_safety_wit_39 : energyNecklace_safety_wit_39
  proof_of_energyNecklace_safety_wit_40 : energyNecklace_safety_wit_40
  proof_of_energyNecklace_safety_wit_41 : energyNecklace_safety_wit_41
  proof_of_energyNecklace_safety_wit_42 : energyNecklace_safety_wit_42
  proof_of_energyNecklace_safety_wit_43 : energyNecklace_safety_wit_43
  proof_of_energyNecklace_safety_wit_44 : energyNecklace_safety_wit_44
  proof_of_energyNecklace_safety_wit_45 : energyNecklace_safety_wit_45
  proof_of_energyNecklace_entail_wit_1 : energyNecklace_entail_wit_1
  proof_of_energyNecklace_entail_wit_11 : energyNecklace_entail_wit_11
  proof_of_energyNecklace_entail_wit_18 : energyNecklace_entail_wit_18
  proof_of_energyNecklace_entail_wit_21 : energyNecklace_entail_wit_21
  proof_of_energyNecklace_entail_wit_23 : energyNecklace_entail_wit_23
  proof_of_energyNecklace_entail_wit_29 : energyNecklace_entail_wit_29
  proof_of_energyNecklace_partial_solve_wit_1 : energyNecklace_partial_solve_wit_1
  proof_of_energyNecklace_partial_solve_wit_2 : energyNecklace_partial_solve_wit_2
  proof_of_energyNecklace_partial_solve_wit_3 : energyNecklace_partial_solve_wit_3
  proof_of_energyNecklace_partial_solve_wit_4 : energyNecklace_partial_solve_wit_4
  proof_of_energyNecklace_partial_solve_wit_5 : energyNecklace_partial_solve_wit_5
  proof_of_energyNecklace_partial_solve_wit_6 : energyNecklace_partial_solve_wit_6
  proof_of_energyNecklace_partial_solve_wit_7 : energyNecklace_partial_solve_wit_7
  proof_of_energyNecklace_partial_solve_wit_8 : energyNecklace_partial_solve_wit_8
  proof_of_energyNecklace_partial_solve_wit_9 : energyNecklace_partial_solve_wit_9
  proof_of_energyNecklace_partial_solve_wit_10 : energyNecklace_partial_solve_wit_10
  proof_of_energyNecklace_partial_solve_wit_11 : energyNecklace_partial_solve_wit_11
  proof_of_energyNecklace_partial_solve_wit_12 : energyNecklace_partial_solve_wit_12
  proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25
  proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27
  proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31
  proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32
  proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2
  proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3
  proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4
  proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5
  proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6
  proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7
  proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8
  proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9
  proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10
  proof_of_energyNecklace_entail_wit_12 : energyNecklace_entail_wit_12
  proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13
  proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14
  proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15
  proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16
  proof_of_energyNecklace_entail_wit_17_1 : energyNecklace_entail_wit_17_1
  proof_of_energyNecklace_entail_wit_17_2 : energyNecklace_entail_wit_17_2
  proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19
  proof_of_energyNecklace_entail_wit_20 : energyNecklace_entail_wit_20
  proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22
  proof_of_energyNecklace_entail_wit_24 : energyNecklace_entail_wit_24
  proof_of_energyNecklace_entail_wit_25 : energyNecklace_entail_wit_25
  proof_of_energyNecklace_entail_wit_26 : energyNecklace_entail_wit_26
  proof_of_energyNecklace_entail_wit_27 : energyNecklace_entail_wit_27
  proof_of_energyNecklace_entail_wit_28_1 : energyNecklace_entail_wit_28_1
  proof_of_energyNecklace_entail_wit_28_2 : energyNecklace_entail_wit_28_2
  proof_of_energyNecklace_entail_wit_30 : energyNecklace_entail_wit_30
  proof_of_energyNecklace_return_wit_1 : energyNecklace_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_goal
