import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib
open SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance super_piano_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def build_prefix_safety_wit_1 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps)) (PreH5 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full pre_pre (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_prefix_safety_wit_2 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps)) (PreH5 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full pre_pre (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_prefix_safety_wit_3 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((Zlength (pref)) = 1)) (PreH5 : ((Znth (0 : Int) pref (0 : Int)) = (0 : Int))) (PreH6 : (PrefixArrayPrefix l pref (0 : Int))) (PreH7 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) 1 pref)
  ** (intArray.undef_seg pre_pre 1 (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_prefix_safety_wit_4 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_prefix_safety_wit_5 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_prefix_safety_wit_6 : Prop :=
  (
forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ (((Znth (i - (0 : Int)) pref (0 : Int)) + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) pref (0 : Int)) + (Znth i l (0 : Int)))) ”
) \/
(
forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ (((Znth (i - (0 : Int)) pref (0 : Int)) + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) pref (0 : Int)) + (Znth i l (0 : Int)))) ”
)

noncomputable def build_prefix_safety_wit_6_split_goal_1 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ (((Znth (i - (0 : Int)) pref (0 : Int)) + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def build_prefix_safety_wit_6_split_goal_2 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) pref (0 : Int)) + (Znth i l (0 : Int)))) ”

noncomputable def build_prefix_safety_wit_7 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.seg pre_pre (0 : Int) ((i + 1) + 1) (pref ++ (((Znth (i - (0 : Int)) pref (0 : Int)) + (Znth i l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg pre_pre ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_prefix_entail_wit_1 : Prop :=
  (
forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps)) (PreH5 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_2 ps (0 : Int))) ∧ ((Znth idx_2 ps (0 : Int)) <= INT_MAX)))) (PreH6 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l (0 : Int))) ∧ ((Znth idx_3 l (0 : Int)) <= 1000)))) ,
  (((pre_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg pre_pre 1 (n_pre + 1))
  ** (intArray.full arr_pre n_pre l)
|--
  EX pref : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (pref)) = 1) ” &&
  “ ((Znth (0 : Int) pref (0 : Int)) = (0 : Int)) ” &&
  “ (PrefixArrayPrefix l pref (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) 1 pref)
  ** (intArray.undef_seg pre_pre 1 (n_pre + 1))
) \/
(
forall (pre_pre : Int) (n_pre : Int) (l : (List Int)) (ps : (List Int)) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (PrefixSums l ps)) (PreH7 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_2 ps (0 : Int))) ∧ ((Znth idx_2 ps (0 : Int)) <= INT_MAX)))) (PreH8 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l (0 : Int))) ∧ ((Znth idx_3 l (0 : Int)) <= 1000)))) ,
  (((pre_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
|--
  EX pref : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (pref)) = 1) ” &&
  “ ((Znth (0 : Int) pref (0 : Int)) = (0 : Int)) ” &&
  “ (PrefixArrayPrefix l pref (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.seg pre_pre (0 : Int) 1 pref)
)

noncomputable def build_prefix_entail_wit_2 : Prop :=
  (
forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref_2 : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((Zlength (pref_2)) = 1)) (PreH5 : ((Znth (0 : Int) pref_2 (0 : Int)) = (0 : Int))) (PreH6 : (PrefixArrayPrefix l pref_2 (0 : Int))) (PreH7 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) 1 pref_2)
  ** (intArray.undef_seg pre_pre 1 (n_pre + 1))
|--
  EX pref : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (PrefixArrayPrefix l pref (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) ((0 : Int) + 1) pref)
  ** (intArray.undef_seg pre_pre ((0 : Int) + 1) (n_pre + 1))
) \/
(
forall (pre_pre : Int) (n_pre : Int) (l : (List Int)) (pref_2 : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((Zlength (pref_2)) = 1)) (PreH5 : ((Znth (0 : Int) pref_2 (0 : Int)) = (0 : Int))) (PreH6 : (PrefixArrayPrefix l pref_2 (0 : Int))) (PreH7 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.seg pre_pre (0 : Int) 1 pref_2)
|--
  EX pref : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (PrefixArrayPrefix l pref (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.seg pre_pre (0 : Int) ((0 : Int) + 1) pref)
)

noncomputable def build_prefix_entail_wit_3 : Prop :=
  (
forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref_2 i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.seg pre_pre (0 : Int) ((i + 1) + 1) (pref_2 ++ (((Znth (i - (0 : Int)) pref_2 (0 : Int)) + (Znth i l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg pre_pre ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full arr_pre n_pre l)
|--
  EX pref : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (PrefixArrayPrefix l pref (i + 1)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) ((i + 1) + 1) pref)
  ** (intArray.undef_seg pre_pre ((i + 1) + 1) (n_pre + 1))
) \/
(
forall (n_pre : Int) (l : (List Int)) (pref_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref_2 i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  “ (PrefixArrayPrefix l (pref_2 ++ (((Znth (i - (0 : Int)) pref_2 (0 : Int)) + (Znth i l (0 : Int))) :: (@List.nil Int))) (i + 1)) ”
  &&  emp
)

noncomputable def build_prefix_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (pref_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref_2 i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (PrefixArrayPrefix l (pref_2 ++ (((Znth (i - (0 : Int)) pref_2 (0 : Int)) + (Znth i l (0 : Int))) :: (@List.nil Int))) (i + 1))

noncomputable def build_prefix_return_wit_1 : Prop :=
  (
forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  EX ps : (List Int),
  “ (PrefixSums l ps) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full pre_pre (n_pre + 1) ps)
) \/
(
forall (pre_pre : Int) (n_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.seg pre_pre (0 : Int) (i + 1) pref)
|--
  EX ps : (List Int),
  “ (PrefixSums l ps) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ”
  &&  (intArray.full pre_pre (n_pre + 1) ps)
)

noncomputable def build_prefix_partial_solve_wit_1 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps)) (PreH5 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full pre_pre (n_pre + 1))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (((pre_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg pre_pre 1 (n_pre + 1))
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_prefix_partial_solve_wit_2 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (PrefixArrayPrefix l pref i) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((pre_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - (0 : Int)) pref (0 : Int))))
  ** (intArray.missing_i pre_pre i (0 : Int) (i + 1) pref)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))

noncomputable def build_prefix_partial_solve_wit_3 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (PrefixArrayPrefix l pref i) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))

noncomputable def build_prefix_partial_solve_wit_4 : Prop :=
  forall (pre_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pref : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)
  ** (intArray.undef_seg pre_pre (i + 1) (n_pre + 1))
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (PrefixArrayPrefix l pref i) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((pre_pre + ((i + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg pre_pre ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.seg pre_pre (0 : Int) (i + 1) pref)

noncomputable def superPiano_safety_wit_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH12 : ((-9223372036854775808) <= ans)) (PreH13 : (ans <= 9223372036854775807)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
|--
  “ (((n_pre + k_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n_pre + k_pre) + 1)) ”

noncomputable def superPiano_safety_wit_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH12 : ((-9223372036854775808) <= ans)) (PreH13 : (ans <= 9223372036854775807)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
|--
  “ ((n_pre + k_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + k_pre)) ”

noncomputable def superPiano_safety_wit_3 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH12 : ((-9223372036854775808) <= ans)) (PreH13 : (ans <= 9223372036854775807)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_4 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (heap_cap : Int) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS))) (PreH12 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def superPiano_safety_wit_5 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (heap_cap : Int) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS))) (PreH12 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_6 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (heap_cap : Int) (hsize : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : (hsize = ((n_pre - L_pre) + 1))) (PreH10 : ((hsize + k_pre) < heap_cap)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (PrefixSums l ps)) (PreH13 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH14 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH15 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH16 : ((Zlength (slots)) = heap_cap)) (PreH17 : (NodeArrays slots vals starts los his bests)) (PreH18 : (NodeHeapState slots hsize)) (PreH19 : (InitialFrontierState ps n_pre L_pre R_pre (sublist ((0 : Int)) (hsize) (slots)))) (PreH20 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "total" ) )) # Int64 |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_7 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (heap_cap : Int) (hsize : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : (hsize = ((n_pre - L_pre) + 1))) (PreH10 : ((hsize + k_pre) < heap_cap)) (PreH11 : (total = (0 : Int))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (PrefixSums l ps)) (PreH14 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH15 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (slots)) = heap_cap)) (PreH18 : (NodeArrays slots vals starts los his bests)) (PreH19 : (NodeHeapState slots hsize)) (PreH20 : (FrontierState ps n_pre L_pre R_pre (@List.nil Int) (0 : Int) (0 : Int) (sublist ((0 : Int)) (hsize) (slots)))) (PreH21 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "t" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_8 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((hsize - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (hsize - 1)) ”

noncomputable def superPiano_safety_wit_9 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_10 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((total + value) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + value)) ”
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((total + value) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + value)) ”
)

noncomputable def superPiano_safety_wit_10_split_goal_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((total + value) <= 9223372036854775807) ”

noncomputable def superPiano_safety_wit_10_split_goal_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((-9223372036854775808) <= (total + value)) ”

noncomputable def superPiano_safety_wit_11 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "has_left" ) )) # Int |->_)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_12 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "left_best" ) )) # Int |->_)
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_13 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_14 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "has_right" ) )) # Int |->_)
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_15 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_best" ) )) # Int |->_)
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_16 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps)) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def superPiano_safety_wit_17 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l query_ps)) (PreH20 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ ((best - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best - 1)) ”

noncomputable def superPiano_safety_wit_18 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize - 1))) (PreH4 : (FrontierPopTop pop_slots hsize slots_out)) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre) + 1) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l query_ps)) (PreH20 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH21 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests)) (PreH24 : ((0 : Int) <= t)) (PreH25 : (t < k_pre)) (PreH26 : ((0 : Int) < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t)) < heap_cap)) (PreH29 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH30 : (NodeHeapState pop_slots hsize)) (PreH31 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : ((0 : Int) <= (start - 1))) (PreH35 : ((start - 1) < (n_pre + 1))) (PreH36 : (((start + L_pre) - 1) <= lo)) (PreH37 : ((0 : Int) <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_19 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo <= (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ ((best - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best - 1)) ”

noncomputable def superPiano_safety_wit_20 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo <= (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def superPiano_safety_wit_21 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo <= (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_22 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo <= (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_23 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”
)

noncomputable def superPiano_safety_wit_23_split_goal_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ”

noncomputable def superPiano_safety_wit_23_split_goal_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”

noncomputable def superPiano_safety_wit_24 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((start - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start - 1)) ”

noncomputable def superPiano_safety_wit_25 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_26 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_27 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo > (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ ((best + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best + 1)) ”

noncomputable def superPiano_safety_wit_28 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((best + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best + 1)) ”

noncomputable def superPiano_safety_wit_29 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_30 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo > (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_31 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((best + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best + 1)) ”

noncomputable def superPiano_safety_wit_32 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def superPiano_safety_wit_33 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_34 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_35 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) <= hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ ((best + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best + 1)) ”

noncomputable def superPiano_safety_wit_36 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) <= hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def superPiano_safety_wit_37 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) <= hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_38 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) <= hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_39 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval_2 : Int) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval_2)) (PreH9 : ((0 : Int) <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval_2 query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval_2))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval_2 : Int) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval_2)) (PreH9 : ((0 : Int) <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval_2 query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval_2))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”
)

noncomputable def superPiano_safety_wit_39_split_goal_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval_2 : Int) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval_2)) (PreH9 : ((0 : Int) <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval_2 query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval_2))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ”

noncomputable def superPiano_safety_wit_39_split_goal_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval_2 : Int) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval_2)) (PreH9 : ((0 : Int) <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval_2 query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval_2))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”

noncomputable def superPiano_safety_wit_40 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval_2)) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1))) (PreH4 : ((best + 1) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH9 : ((0 : Int) <= retval)) (PreH10 : (retval < (n_pre + 1))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval_2))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((start - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start - 1)) ”

noncomputable def superPiano_safety_wit_41 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval_2)) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1))) (PreH4 : ((best + 1) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH9 : ((0 : Int) <= retval)) (PreH10 : (retval < (n_pre + 1))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval_2))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_42 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”
)

noncomputable def superPiano_safety_wit_42_split_goal_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) <= INT_MAX) ”

noncomputable def superPiano_safety_wit_42_split_goal_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((INT_MIN) <= ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) ”

noncomputable def superPiano_safety_wit_43 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((start - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start - 1)) ”

noncomputable def superPiano_safety_wit_44 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_45 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval_2)) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1))) (PreH4 : ((best + 1) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH9 : ((0 : Int) <= retval)) (PreH10 : (retval < (n_pre + 1))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> (((Znth retval_2 query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "right_best" ) )) # Int |-> (retval_2))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_46 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "right_best" ) )) # Int |-> (retval))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_47 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : ((best + 1) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ ((best - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best - 1)) ”

noncomputable def superPiano_safety_wit_48 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : ((best + 1) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_49 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = (0 : Int))) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (hi <= best)) (PreH40 : (right_best = (0 : Int))) (PreH41 : (right_value = (0 : Int))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ ((best - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best - 1)) ”

noncomputable def superPiano_safety_wit_50 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = (0 : Int))) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (hi <= best)) (PreH40 : (right_best = (0 : Int))) (PreH41 : (right_value = (0 : Int))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_51 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps)) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH27 : (NodeHeapState push_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= (best - 1))) (PreH34 : ((best + 1) <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH38 : ((0 : Int) <= left_best)) (PreH39 : (left_best < (n_pre + 1))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH43 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH44 : ((0 : Int) <= right_best)) (PreH45 : (right_best < (n_pre + 1))) (PreH46 : ((best + 1) <= right_best)) (PreH47 : (right_best <= hi)) (PreH48 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((hsize + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (hsize + 1)) ”

noncomputable def superPiano_safety_wit_52 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps)) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH27 : (NodeHeapState push_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= (best - 1))) (PreH34 : ((best + 1) <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH38 : ((0 : Int) <= left_best)) (PreH39 : (left_best < (n_pre + 1))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH43 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH44 : ((0 : Int) <= right_best)) (PreH45 : (right_best < (n_pre + 1))) (PreH46 : ((best + 1) <= right_best)) (PreH47 : (right_best <= hi)) (PreH48 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH50 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_53 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps)) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = (0 : Int))) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH27 : (NodeHeapState push_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= (best - 1))) (PreH34 : (best <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH38 : ((0 : Int) <= left_best)) (PreH39 : (left_best < (n_pre + 1))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH43 : (hi <= best)) (PreH44 : (right_best = (0 : Int))) (PreH45 : (right_value = (0 : Int))) (PreH46 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH47 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((hsize + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (hsize + 1)) ”

noncomputable def superPiano_safety_wit_54 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps)) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = (0 : Int))) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH27 : (NodeHeapState push_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= (best - 1))) (PreH34 : (best <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH38 : ((0 : Int) <= left_best)) (PreH39 : (left_best < (n_pre + 1))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH43 : (hi <= best)) (PreH44 : (right_best = (0 : Int))) (PreH45 : (right_value = (0 : Int))) (PreH46 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH47 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_55 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left = (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ False ”

noncomputable def superPiano_safety_wit_56 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left = (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = (0 : Int))) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (hi <= best)) (PreH45 : (right_best = (0 : Int))) (PreH46 : (right_value = (0 : Int))) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ False ”

noncomputable def superPiano_safety_wit_57 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) (PreH52 : (has_right = (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ False ”

noncomputable def superPiano_safety_wit_58 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (left_best : Int) (left_value : Int) (right_best : Int) (right_value : Int) (t : Int) (hsize : Int) (total : Int) (best : Int) (start : Int) (lo : Int) (hi : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals starts los his bests)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (has_right = (0 : Int))) (PreH17 : (left_best = (0 : Int))) (PreH18 : (left_value = (0 : Int))) (PreH19 : (right_best = (0 : Int))) (PreH20 : (right_value = (0 : Int))) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1))) < heap_cap)) (PreH26 : (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) (hsize) (slots)))) (PreH27 : (NodeHeapState slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH35 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) (PreH36 : (has_right ≠ (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ False ”

noncomputable def superPiano_safety_wit_59 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = (0 : Int))) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (hi <= best)) (PreH45 : (right_best = (0 : Int))) (PreH46 : (right_value = (0 : Int))) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) (PreH49 : (has_right ≠ (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ False ”

noncomputable def superPiano_safety_wit_60 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) (PreH52 : (has_right ≠ (0 : Int))) (PreH53 : (has_left = (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ False ”

noncomputable def superPiano_safety_wit_61 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH23 : (NodeHeapState right_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1) <= hi)) (PreH31 : ((0 : Int) <= (best + 1))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH34 : ((0 : Int) <= right_best)) (PreH35 : (right_best < (n_pre + 1))) (PreH36 : ((best + 1) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= (best - 1))) (PreH41 : ((best - 1) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH43 : ((0 : Int) <= left_best)) (PreH44 : (left_best < (n_pre + 1))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ ((best + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best + 1)) ”

noncomputable def superPiano_safety_wit_62 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH23 : (NodeHeapState right_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1) <= hi)) (PreH31 : ((0 : Int) <= (best + 1))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH34 : ((0 : Int) <= right_best)) (PreH35 : (right_best < (n_pre + 1))) (PreH36 : ((best + 1) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= (best - 1))) (PreH41 : ((best - 1) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH43 : ((0 : Int) <= left_best)) (PreH44 : (left_best < (n_pre + 1))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_63 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (left_best = (0 : Int))) (PreH17 : (left_value = (0 : Int))) (PreH18 : (has_right = 1)) (PreH19 : ((0 : Int) <= t)) (PreH20 : (t < k_pre)) (PreH21 : ((0 : Int) <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH25 : (NodeHeapState right_slots hsize)) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : ((0 : Int) <= (start - 1))) (PreH29 : ((start - 1) < (n_pre + 1))) (PreH30 : ((0 : Int) <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1) <= hi)) (PreH33 : ((0 : Int) <= (best + 1))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH36 : ((0 : Int) <= right_best)) (PreH37 : (right_best < (n_pre + 1))) (PreH38 : ((best + 1) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ ((best + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best + 1)) ”

noncomputable def superPiano_safety_wit_64 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (left_best = (0 : Int))) (PreH17 : (left_value = (0 : Int))) (PreH18 : (has_right = 1)) (PreH19 : ((0 : Int) <= t)) (PreH20 : (t < k_pre)) (PreH21 : ((0 : Int) <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH25 : (NodeHeapState right_slots hsize)) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : ((0 : Int) <= (start - 1))) (PreH29 : ((start - 1) < (n_pre + 1))) (PreH30 : ((0 : Int) <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1) <= hi)) (PreH33 : ((0 : Int) <= (best + 1))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH36 : ((0 : Int) <= right_best)) (PreH37 : (right_best < (n_pre + 1))) (PreH38 : ((best + 1) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_65 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH27 : (NodeHeapState right_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1) <= hi)) (PreH35 : ((0 : Int) <= (best + 1))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH38 : ((0 : Int) <= right_best)) (PreH39 : (right_best < (n_pre + 1))) (PreH40 : ((best + 1) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH43 : ((0 : Int) <= lo)) (PreH44 : (lo <= (best - 1))) (PreH45 : ((best - 1) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH47 : ((0 : Int) <= left_best)) (PreH48 : (left_best < (n_pre + 1))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH53 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((hsize + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (hsize + 1)) ”

noncomputable def superPiano_safety_wit_66 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH27 : (NodeHeapState right_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1) <= hi)) (PreH35 : ((0 : Int) <= (best + 1))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH38 : ((0 : Int) <= right_best)) (PreH39 : (right_best < (n_pre + 1))) (PreH40 : ((best + 1) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH43 : ((0 : Int) <= lo)) (PreH44 : (lo <= (best - 1))) (PreH45 : ((best - 1) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH47 : ((0 : Int) <= left_best)) (PreH48 : (left_best < (n_pre + 1))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH53 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_67 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = (0 : Int))) (PreH20 : (left_best = (0 : Int))) (PreH21 : (left_value = (0 : Int))) (PreH22 : (has_right = 1)) (PreH23 : ((0 : Int) <= t)) (PreH24 : (t < k_pre)) (PreH25 : ((0 : Int) <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH29 : (NodeHeapState right_slots hsize)) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : ((0 : Int) <= (start - 1))) (PreH33 : ((start - 1) < (n_pre + 1))) (PreH34 : ((0 : Int) <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1) <= hi)) (PreH37 : ((0 : Int) <= (best + 1))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((hsize + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (hsize + 1)) ”

noncomputable def superPiano_safety_wit_68 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = (0 : Int))) (PreH20 : (left_best = (0 : Int))) (PreH21 : (left_value = (0 : Int))) (PreH22 : (has_right = 1)) (PreH23 : ((0 : Int) <= t)) (PreH24 : (t < k_pre)) (PreH25 : ((0 : Int) <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH29 : (NodeHeapState right_slots hsize)) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : ((0 : Int) <= (start - 1))) (PreH33 : ((start - 1) < (n_pre + 1))) (PreH34 : ((0 : Int) <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1) <= hi)) (PreH37 : ((0 : Int) <= (best + 1))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def superPiano_safety_wit_69 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (left_best : Int) (right_best : Int) (left_value : Int) (right_value : Int) (t : Int) (hsize : Int) (total : Int) (best : Int) (start : Int) (hi : Int) (lo : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals starts los his bests)) (PreH15 : ((0 : Int) <= has_left)) (PreH16 : (has_left <= 1)) (PreH17 : ((0 : Int) <= has_right)) (PreH18 : (has_right <= 1)) (PreH19 : ((0 : Int) <= left_best)) (PreH20 : (left_best < (n_pre + 1))) (PreH21 : ((0 : Int) <= right_best)) (PreH22 : (right_best < (n_pre + 1))) (PreH23 : (INT_MIN <= left_value)) (PreH24 : (left_value <= INT_MAX)) (PreH25 : (INT_MIN <= right_value)) (PreH26 : (right_value <= INT_MAX)) (PreH27 : ((0 : Int) <= t)) (PreH28 : (t < k_pre)) (PreH29 : ((0 : Int) <= hsize)) (PreH30 : (hsize < heap_cap)) (PreH31 : ((hsize + (k_pre - (t + 1))) < heap_cap)) (PreH32 : (FrontierState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) (hsize) (slots)))) (PreH33 : (NodeHeapState slots hsize)) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH35 : (1 <= start)) (PreH36 : (start <= n_pre)) (PreH37 : ((0 : Int) <= (start - 1))) (PreH38 : ((start - 1) < (n_pre + 1))) (PreH39 : (((start + L_pre) - 1) <= lo)) (PreH40 : ((0 : Int) <= lo)) (PreH41 : (lo <= best)) (PreH42 : (best <= hi)) (PreH43 : (hi <= n_pre)) (PreH44 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ ((t + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (t + 1)) ”

noncomputable def superPiano_entail_wit_1 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (ps_3 : (List Int)) (PreH1 : (PrefixSums l ps_3)) (PreH2 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_3 (0 : Int))) ∧ ((Znth idx_3 ps_3 (0 : Int)) <= INT_MAX)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= L_pre)) (PreH6 : (L_pre <= R_pre)) (PreH7 : (R_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (((n_pre + k_pre) + 1) <= 200000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2)) (PreH12 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_4 ps_2 (0 : Int))) ∧ ((Znth idx_4 ps_2 (0 : Int)) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH14 : ((-9223372036854775808) <= ans_2)) (PreH15 : (ans_2 <= 9223372036854775807)) (PreH16 : forall (idx_5 : Int) , ((((0 : Int) <= idx_5) ∧ (idx_5 < n_pre)) -> (((-1000) <= (Znth idx_5 l (0 : Int))) ∧ ((Znth idx_5 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps_3)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
|--
  EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (((n_pre + k_pre) + 1) = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (ps_3 : (List Int)) (PreH1 : (PrefixSums l ps_3)) (PreH2 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_3 (0 : Int))) ∧ ((Znth idx_3 ps_3 (0 : Int)) <= INT_MAX)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= L_pre)) (PreH6 : (L_pre <= R_pre)) (PreH7 : (R_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (((n_pre + k_pre) + 1) <= 200000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2)) (PreH12 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_4 ps_2 (0 : Int))) ∧ ((Znth idx_4 ps_2 (0 : Int)) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH14 : ((-9223372036854775808) <= ans_2)) (PreH15 : (ans_2 <= 9223372036854775807)) (PreH16 : forall (idx_5 : Int) , ((((0 : Int) <= idx_5) ∧ (idx_5 < n_pre)) -> (((-1000) <= (Znth idx_5 l (0 : Int))) ∧ ((Znth idx_5 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX ans : Int, EX st_slots : (List Int),
  “ ((Zlength (st_slots)) = (((Zlength (l)) + 1) * ST_LEVELS)) ” &&
  “ (SuperPianoAnswerByPrefix ps_3 (Zlength (l)) L_pre R_pre k_pre ans) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (heap_cap : Int) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (st_out : (List Int)) (PreH1 : (SparseArgmaxBuilt ps_2 st_out (n_pre + 1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre) + 1) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2)) (PreH12 : ((Zlength (st_slots_2)) = ((n_pre + 1) * ST_LEVELS))) (PreH13 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH14 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH15 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)

noncomputable def superPiano_entail_wit_3 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (heap_cap : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (retval : Int) (PreH1 : (retval = ((n_pre - L_pre) + 1))) (PreH2 : ((Zlength (slots_2)) = heap_cap)) (PreH3 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH4 : (NodeHeapState slots_2 retval)) (PreH5 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist ((0 : Int)) (retval) (slots_2)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps_2)) (PreH16 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH17 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH18 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH19 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
  ** (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
  ** (intArray.full arr_pre n_pre l)
|--
  EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ (retval = ((n_pre - L_pre) + 1)) ” &&
  “ ((retval + k_pre) < heap_cap) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots retval) ” &&
  “ (InitialFrontierState ps n_pre L_pre R_pre (sublist ((0 : Int)) (retval) (slots))) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (heap_cap : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (retval : Int) (PreH1 : (retval = ((n_pre - L_pre) + 1))) (PreH2 : ((Zlength (slots_2)) = heap_cap)) (PreH3 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH4 : (NodeHeapState slots_2 retval)) (PreH5 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist ((0 : Int)) (retval) (slots_2)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps_2)) (PreH16 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH17 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH18 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH19 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (((((Zlength (l)) - L_pre) + 1) + k_pre) < (Zlength (slots_2))) ” &&
  “ ((Zlength (slots)) = (Zlength (slots_2))) ” &&
  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2) ” &&
  “ (NodeHeapState slots (((Zlength (l)) - L_pre) + 1)) ” &&
  “ (InitialFrontierState ps_2 (Zlength (l)) L_pre R_pre (sublist ((0 : Int)) ((((Zlength (l)) - L_pre) + 1)) (slots))) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_4 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (heap_cap : Int) (hsize : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : (hsize = ((n_pre - L_pre) + 1))) (PreH10 : ((hsize + k_pre) < heap_cap)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (PrefixSums l ps_2)) (PreH13 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH14 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH15 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH16 : ((Zlength (slots_2)) = heap_cap)) (PreH17 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH18 : (NodeHeapState slots_2 hsize)) (PreH19 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH20 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
  ** (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
|--
  EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ (hsize = ((n_pre - L_pre) + 1)) ” &&
  “ ((hsize + k_pre) < heap_cap) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (FrontierState ps n_pre L_pre R_pre (@List.nil Int) (0 : Int) (0 : Int) (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (heap_cap : Int) (hsize : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : (hsize = ((n_pre - L_pre) + 1))) (PreH10 : ((hsize + k_pre) < heap_cap)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (PrefixSums l ps_2)) (PreH13 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH14 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH15 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH16 : ((Zlength (slots_2)) = heap_cap)) (PreH17 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH18 : (NodeHeapState slots_2 hsize)) (PreH19 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH20 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2) ” &&
  “ (NodeHeapState slots (((Zlength (l)) - L_pre) + 1)) ” &&
  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre (@List.nil Int) (0 : Int) (0 : Int) (sublist ((0 : Int)) ((((Zlength (l)) - L_pre) + 1)) (slots))) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_5 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (heap_cap : Int) (hsize : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : (hsize = ((n_pre - L_pre) + 1))) (PreH10 : ((hsize + k_pre) < heap_cap)) (PreH11 : (total = (0 : Int))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (PrefixSums l ps_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_2 ps_2 (0 : Int))) ∧ ((Znth idx_2 ps_2 (0 : Int)) <= INT_MAX)))) (PreH15 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH17 : ((Zlength (slots_2)) = heap_cap)) (PreH18 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH19 : (NodeHeapState slots_2 hsize)) (PreH20 : (FrontierState ps_2 n_pre L_pre R_pre (@List.nil Int) (0 : Int) (0 : Int) (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH21 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l (0 : Int))) ∧ ((Znth idx_3 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
  ** (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - (0 : Int))) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen (0 : Int) total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (((0 : Int) < k_pre) -> ((0 : Int) < hsize)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (heap_cap : Int) (hsize : Int) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : (hsize = ((n_pre - L_pre) + 1))) (PreH10 : ((hsize + k_pre) < heap_cap)) (PreH11 : (total = (0 : Int))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (PrefixSums l ps_2)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_2 ps_2 (0 : Int))) ∧ ((Znth idx_2 ps_2 (0 : Int)) <= INT_MAX)))) (PreH15 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH17 : ((Zlength (slots_2)) = heap_cap)) (PreH18 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH19 : (NodeHeapState slots_2 hsize)) (PreH20 : (FrontierState ps_2 n_pre L_pre R_pre (@List.nil Int) (0 : Int) (0 : Int) (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH21 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l (0 : Int))) ∧ ((Znth idx_3 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= k_pre) ” &&
  “ ((0 : Int) <= (((Zlength (l)) - L_pre) + 1)) ” &&
  “ ((((Zlength (l)) - L_pre) + 1) <= (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (((((Zlength (l)) - L_pre) + 1) + (k_pre - (0 : Int))) < (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre chosen (0 : Int) (0 : Int) (sublist ((0 : Int)) ((((Zlength (l)) - L_pre) + 1)) (slots))) ” &&
  “ (NodeHeapState slots (((Zlength (l)) - L_pre) + 1)) ” &&
  “ (((0 : Int) < k_pre) -> ((0 : Int) < (((Zlength (l)) - L_pre) + 1))) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_6 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans_2 : Int) (st_slots_2 : (List Int)) (ps_2 : (List Int)) (heap_cap : Int) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (retval : Int) (retval_2 : Int) (retval_3 : Int) (retval_4 : Int) (retval_5 : Int) (PreH1 : (retval_5 = (heap_top_best (slots_2)))) (PreH2 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH3 : (NodeHeapState slots_2 hsize)) (PreH4 : (retval_4 = (heap_top_hi (slots_2)))) (PreH5 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH6 : (NodeHeapState slots_2 hsize)) (PreH7 : (retval_3 = (heap_top_lo (slots_2)))) (PreH8 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH9 : (NodeHeapState slots_2 hsize)) (PreH10 : (retval_2 = (heap_top_start (slots_2)))) (PreH11 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH12 : (NodeHeapState slots_2 hsize)) (PreH13 : (retval = (heap_top_value (slots_2)))) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH15 : (NodeHeapState slots_2 hsize)) (PreH16 : (t < k_pre)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l ps_2)) (PreH27 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH29 : ((Zlength (slots_2)) = heap_cap)) (PreH30 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t <= k_pre)) (PreH33 : ((0 : Int) <= hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH37 : (NodeHeapState slots_2 hsize)) (PreH38 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH39 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (retval = (heap_top_value (slots))) ” &&
  “ (retval_2 = (heap_top_start (slots))) ” &&
  “ (retval_3 = (heap_top_lo (slots))) ” &&
  “ (retval_4 = (heap_top_hi (slots))) ” &&
  “ (retval_5 = (heap_top_best (slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre retval retval_2 retval_3 retval_4 retval_5) ” &&
  “ (1 <= retval_2) ” &&
  “ (retval_2 <= n_pre) ” &&
  “ ((0 : Int) <= (retval_2 - 1)) ” &&
  “ ((retval_2 - 1) < (n_pre + 1)) ” &&
  “ (((retval_2 + L_pre) - 1) <= retval_3) ” &&
  “ ((0 : Int) <= retval_3) ” &&
  “ (retval_3 <= retval_5) ” &&
  “ (retval_5 <= retval_4) ” &&
  “ (retval_4 <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans_2 : Int) (st_slots_2 : (List Int)) (ps_2 : (List Int)) (heap_cap : Int) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (retval : Int) (retval_2 : Int) (retval_3 : Int) (retval_4 : Int) (retval_5 : Int) (PreH1 : (retval_5 = (heap_top_best (slots_2)))) (PreH2 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH3 : (NodeHeapState slots_2 hsize)) (PreH4 : (retval_4 = (heap_top_hi (slots_2)))) (PreH5 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH6 : (NodeHeapState slots_2 hsize)) (PreH7 : (retval_3 = (heap_top_lo (slots_2)))) (PreH8 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH9 : (NodeHeapState slots_2 hsize)) (PreH10 : (retval_2 = (heap_top_start (slots_2)))) (PreH11 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH12 : (NodeHeapState slots_2 hsize)) (PreH13 : (retval = (heap_top_value (slots_2)))) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH15 : (NodeHeapState slots_2 hsize)) (PreH16 : (t < k_pre)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l ps_2)) (PreH27 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH29 : ((Zlength (slots_2)) = heap_cap)) (PreH30 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t <= k_pre)) (PreH33 : ((0 : Int) <= hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH37 : (NodeHeapState slots_2 hsize)) (PreH38 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH39 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((heap_top_value (slots_2)) = (heap_top_value (slots))) ” &&
  “ ((heap_top_start (slots_2)) = (heap_top_start (slots))) ” &&
  “ ((heap_top_lo (slots_2)) = (heap_top_lo (slots))) ” &&
  “ ((heap_top_hi (slots_2)) = (heap_top_hi (slots))) ” &&
  “ ((heap_top_best (slots_2)) = (heap_top_best (slots))) ” &&
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (ValidNodeFields ps_2 (Zlength (l)) L_pre R_pre (heap_top_value (slots_2)) (heap_top_start (slots_2)) (heap_top_lo (slots_2)) (heap_top_hi (slots_2)) (heap_top_best (slots_2))) ” &&
  “ (1 <= (heap_top_start (slots_2))) ” &&
  “ ((heap_top_start (slots_2)) <= (Zlength (l))) ” &&
  “ ((0 : Int) <= ((heap_top_start (slots_2)) - 1)) ” &&
  “ (((heap_top_start (slots_2)) - 1) < ((Zlength (l)) + 1)) ” &&
  “ ((((heap_top_start (slots_2)) + L_pre) - 1) <= (heap_top_lo (slots_2))) ” &&
  “ ((0 : Int) <= (heap_top_lo (slots_2))) ” &&
  “ ((heap_top_lo (slots_2)) <= (heap_top_best (slots_2))) ” &&
  “ ((heap_top_best (slots_2)) <= (heap_top_hi (slots_2))) ” &&
  “ ((heap_top_hi (slots_2)) <= (Zlength (l))) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_7 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval_2)) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1))) (PreH4 : ((best + 1) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH9 : ((0 : Int) <= retval)) (PreH10 : (retval < (n_pre + 1))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (1 = 1) ” &&
  “ (1 = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < heap_cap) ” &&
  “ ((((hsize - 1) + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) (total + value) ((mkNode (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) (start) (lo) ((best - 1)) (retval)) :: ((mkNode (((Znth retval_2 query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) (start) ((best + 1)) (hi) (retval_2)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax ps lo (best - 1) retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ (lo <= retval) ” &&
  “ (retval <= (best - 1)) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) start lo (best - 1) retval) ” &&
  “ (RangeArgmax ps (best + 1) hi retval_2) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval_2) ” &&
  “ (retval_2 <= hi) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval_2 query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) start (best + 1) hi retval_2) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval_2)) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1))) (PreH4 : ((best + 1) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH9 : ((0 : Int) <= retval)) (PreH10 : (retval < (n_pre + 1))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (SparseArgmaxBuilt query_ps query_st_slots ((Zlength (l)) + 1)) ” &&
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < (Zlength (slots_out))) ” &&
  “ ((((hsize - 1) + 1) + (k_pre - t)) < (Zlength (slots_out))) ” &&
  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots)))) :: chosen) (t + 1) (total + (heap_top_value (pop_slots))) ((mkNode (((Znth retval query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int)))) ((heap_top_start (pop_slots))) ((heap_top_lo (pop_slots))) (((heap_top_best (pop_slots)) - 1)) (retval)) :: ((mkNode (((Znth retval_2 query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int)))) ((heap_top_start (pop_slots))) (((heap_top_best (pop_slots)) + 1)) ((heap_top_hi (pop_slots))) (retval_2)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ (((heap_top_best (pop_slots)) - 1) <= (Zlength (l))) ” &&
  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int))) (heap_top_start (pop_slots)) (heap_top_lo (pop_slots)) ((heap_top_best (pop_slots)) - 1) retval) ” &&
  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval_2 query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int))) (heap_top_start (pop_slots)) ((heap_top_best (pop_slots)) + 1) (heap_top_hi (pop_slots)) retval_2) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_8 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) > hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (1 = 1) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < heap_cap) ” &&
  “ ((((hsize - 1) + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) (total + value) ((mkNode (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) (start) (lo) ((best - 1)) (retval)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax ps lo (best - 1) retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ (lo <= retval) ” &&
  “ (retval <= (best - 1)) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) start lo (best - 1) retval) ” &&
  “ (hi <= best) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) > hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (SparseArgmaxBuilt query_ps query_st_slots ((Zlength (l)) + 1)) ” &&
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < (Zlength (slots_out))) ” &&
  “ ((((hsize - 1) + 1) + (k_pre - t)) < (Zlength (slots_out))) ” &&
  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots)))) :: chosen) (t + 1) (total + (heap_top_value (pop_slots))) ((mkNode (((Znth retval query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int)))) ((heap_top_start (pop_slots))) ((heap_top_lo (pop_slots))) (((heap_top_best (pop_slots)) - 1)) (retval)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ (((heap_top_best (pop_slots)) - 1) <= (Zlength (l))) ” &&
  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int))) (heap_top_start (pop_slots)) (heap_top_lo (pop_slots)) ((heap_top_best (pop_slots)) - 1) retval) ” &&
  “ ((heap_top_hi (pop_slots)) <= (heap_top_best (pop_slots))) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_9 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) > hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < heap_cap) ” &&
  “ (((hsize - 1) + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) (total + value) (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (lo = best) ” &&
  “ (best = hi) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) > hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < (Zlength (slots_out))) ” &&
  “ (((hsize - 1) + (k_pre - (t + 1))) < (Zlength (slots_out))) ” &&
  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots)))) :: chosen) (t + 1) (total + (heap_top_value (pop_slots))) (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ ((heap_top_lo (pop_slots)) = (heap_top_best (pop_slots))) ” &&
  “ ((heap_top_best (pop_slots)) = (heap_top_hi (pop_slots))) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_10_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (left_best : Int) (left_value : Int) (right_best : Int) (right_value : Int) (t : Int) (hsize : Int) (total : Int) (best : Int) (start : Int) (lo : Int) (hi : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals starts los his bests)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (has_right = (0 : Int))) (PreH17 : (left_best = (0 : Int))) (PreH18 : (left_value = (0 : Int))) (PreH19 : (right_best = (0 : Int))) (PreH20 : (right_value = (0 : Int))) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1))) < heap_cap)) (PreH26 : (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) (hsize) (slots)))) (PreH27 : (NodeHeapState slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH35 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) (PreH36 : (has_right = (0 : Int))) ,
  ((( &( "hsize" ) )) # Int |-> (hsize))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (has_left = (0 : Int)) ” &&
  “ (has_right = (0 : Int)) ” &&
  “ (left_best = (0 : Int)) ” &&
  “ (left_value = (0 : Int)) ” &&
  “ (right_best = (0 : Int)) ” &&
  “ (right_value = (0 : Int)) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((hsize + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (lo = best) ” &&
  “ (best = hi) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ” &&
  “ (has_right = (0 : Int)) ”
  &&  ((( &( "hsize" ) )) # Int |-> (hsize))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)

noncomputable def superPiano_entail_wit_10_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = (0 : Int))) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (hi <= best)) (PreH45 : (right_best = (0 : Int))) (PreH46 : (right_value = (0 : Int))) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH48 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH49 : (has_right = (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
|--
  “ (has_left ≠ (0 : Int)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize + 1)) ” &&
  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l push_ps) ” &&
  “ (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = (0 : Int)) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots))) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax push_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (hi <= best) ” &&
  “ (right_best = (0 : Int)) ” &&
  “ (right_value = (0 : Int)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ” &&
  “ (has_right = (0 : Int)) ”
  &&  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)

noncomputable def superPiano_entail_wit_10_3 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_3 : Int) (st_slots_3 : (List Int)) (chosen_3 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize_3 : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out_2 : (List Int)) (starts_out_2 : (List Int)) (los_out_2 : (List Int)) (his_out_2 : (List Int)) (bests_out_2 : (List Int)) (slots_out_2 : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out_2)) = heap_cap)) (PreH3 : (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2)) (PreH4 : (NodeHeapState slots_out_2 (hsize_3 + 1))) (PreH5 : (FrontierPushFields push_slots hsize_3 left_value start lo (best - 1) left_best slots_out_2)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_3 (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_3)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize_3)) (PreH25 : (hsize_3 < heap_cap)) (PreH26 : (((hsize_3 + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_3) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize_3) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize_3)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l (0 : Int))) ∧ ((Znth idx_3 l (0 : Int)) <= 1000)))) (PreH52 : (has_right = (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out_2)
  ** (intArray.full heap_start_pre heap_cap starts_out_2)
  ** (intArray.full heap_lo_pre heap_cap los_out_2)
  ** (intArray.full heap_hi_pre heap_cap his_out_2)
  ** (intArray.full heap_best_pre heap_cap bests_out_2)
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_3 + 1)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_3)
|--
  (EX chosen : (List Int), EX hsize : Int, EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (has_left = (0 : Int)) ” &&
  “ (has_right = (0 : Int)) ” &&
  “ (left_best = (0 : Int)) ” &&
  “ (left_value = (0 : Int)) ” &&
  “ (right_best = (0 : Int)) ” &&
  “ (right_value = (0 : Int)) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((hsize + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (lo = best) ” &&
  “ (best = hi) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ” &&
  “ (has_right = (0 : Int)) ”
  &&  ((( &( "hsize" ) )) # Int |-> (hsize))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests))
  ||
  (EX vals_out : (List Int), EX starts_out : (List Int), EX los_out : (List Int), EX his_out : (List Int), EX bests_out : (List Int), EX slots_out : (List ((((Int × Int) × Int) × Int) × Int)), EX chosen_2 : (List Int), EX hsize_2 : Int, EX ans_2 : Int, EX st_slots_2 : (List Int),
  “ (has_left ≠ (0 : Int)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize_2 + 1)) ” &&
  “ (FrontierPushFields push_slots hsize_2 left_value start lo (best - 1) left_best slots_out) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l push_ps) ” &&
  “ (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = (0 : Int)) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize_2) ” &&
  “ (hsize_2 < heap_cap) ” &&
  “ (((hsize_2 + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize_2) (push_slots))) ” &&
  “ (NodeHeapState push_slots hsize_2) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax push_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (hi <= best) ” &&
  “ (right_best = (0 : Int)) ” &&
  “ (right_value = (0 : Int)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ” &&
  “ (has_right = (0 : Int)) ”
  &&  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_2 + 1)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2))

noncomputable def superPiano_entail_wit_11_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (ps : (List Int)) (ans_3 : Int) (st_slots_2 : (List Int)) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_3 : (List Int)) (heap_cap : Int) (has_left_2 : Int) (has_right_2 : Int) (left_best_2 : Int) (left_value_2 : Int) (right_best : Int) (right_value_2 : Int) (t : Int) (hsize_3 : Int) (total_3 : Int) (best : Int) (start : Int) (lo : Int) (hi : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans_3)) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH15 : (has_left_2 = (0 : Int))) (PreH16 : (has_right_2 = (0 : Int))) (PreH17 : (left_best_2 = (0 : Int))) (PreH18 : (left_value_2 = (0 : Int))) (PreH19 : (right_best = (0 : Int))) (PreH20 : (right_value_2 = (0 : Int))) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize_3)) (PreH24 : (hsize_3 < heap_cap)) (PreH25 : ((hsize_3 + (k_pre - (t + 1))) < heap_cap)) (PreH26 : (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_3) (t + 1) total_3 (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) (hsize_3) (slots)))) (PreH27 : (NodeHeapState slots hsize_3)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH35 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l (0 : Int))) ∧ ((Znth idx_3 l (0 : Int)) <= 1000)))) (PreH36 : (has_right_2 ≠ (0 : Int))) ,
  ((( &( "has_left" ) )) # Int |-> (has_left_2))
  ** ((( &( "has_right" ) )) # Int |-> (has_right_2))
  ** ((( &( "left_best" ) )) # Int |-> (left_best_2))
  ** ((( &( "left_value" ) )) # Int |-> (left_value_2))
  ** ((( &( "right_value" ) )) # Int |-> (right_value_2))
  ** ((( &( "hsize" ) )) # Int |-> (hsize_3))
  ** ((( &( "total" ) )) # Int64 |-> (total_3))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
  ** (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
|--
  (EX push_ps : (List Int), EX push_slots : (List ((((Int × Int) × Int) × Int) × Int)), EX push_vals : (List Int), EX push_starts : (List Int), EX push_los : (List Int), EX push_his : (List Int), EX push_bests : (List Int), EX vals_out : (List Int), EX starts_out : (List Int), EX los_out : (List Int), EX his_out : (List Int), EX bests_out : (List Int), EX slots_out : (List ((((Int × Int) × Int) × Int) × Int)), EX chosen : (List Int), EX total : Int, EX left_value : Int, EX left_best : Int, EX right_value : Int, EX hsize : Int, EX has_right : Int, EX has_left : Int, EX ans : Int, EX st_slots : (List Int),
  “ (has_left ≠ (0 : Int)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize + 1)) ” &&
  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l push_ps) ” &&
  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots))) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax push_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (RangeArgmax push_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ” &&
  “ (has_right ≠ (0 : Int)) ”
  &&  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots))
  ||
  (EX ans_2 : Int, EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX chosen_2 : (List Int), EX hsize_2 : Int, EX total_2 : Int, EX vals_out_2 : (List Int), EX starts_out_2 : (List Int), EX los_out_2 : (List Int), EX his_out_2 : (List Int), EX bests_out_2 : (List Int), EX slots_out_2 : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (RangeArgmax query_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out_2)) = heap_cap) ” &&
  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2) ” &&
  “ (NodeHeapState slots_out_2 (hsize_2 - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize_2 slots_out_2) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize_2) ” &&
  “ (hsize_2 <= heap_cap) ” &&
  “ ((hsize_2 + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total_2 (sublist ((0 : Int)) (hsize_2) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize_2) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> (((Znth right_best query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "has_right" ) )) # Int |-> (1))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out_2)
  ** (intArray.full heap_start_pre heap_cap starts_out_2)
  ** (intArray.full heap_lo_pre heap_cap los_out_2)
  ** (intArray.full heap_hi_pre heap_cap his_out_2)
  ** (intArray.full heap_best_pre heap_cap bests_out_2)
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_2 - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total_2 + value)))
  ** (intArray.full arr_pre n_pre l))

noncomputable def superPiano_entail_wit_11_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (ans_3 : Int) (st_slots_2 : (List Int)) (chosen_3 : (List Int)) (heap_cap : Int) (has_left_2 : Int) (has_right_2 : Int) (t : Int) (hsize_3 : Int) (left_best_2 : Int) (best : Int) (lo : Int) (start : Int) (left_value_2 : Int) (total_3 : Int) (hi : Int) (right_best : Int) (right_value_2 : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out_3 : (List Int)) (starts_out_3 : (List Int)) (los_out_3 : (List Int)) (his_out_3 : (List Int)) (bests_out_3 : (List Int)) (slots_out_3 : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left_2 ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out_3)) = heap_cap)) (PreH3 : (NodeArrays slots_out_3 vals_out_3 starts_out_3 los_out_3 his_out_3 bests_out_3)) (PreH4 : (NodeHeapState slots_out_3 (hsize_3 + 1))) (PreH5 : (FrontierPushFields push_slots hsize_3 left_value_2 start lo (best - 1) left_best_2 slots_out_3)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_3)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left_2 = 1)) (PreH21 : (has_right_2 = (0 : Int))) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize_3)) (PreH25 : (hsize_3 < heap_cap)) (PreH26 : (((hsize_3 + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_3) (t + 1) total_3 ((mkNode (left_value_2) (start) (lo) ((best - 1)) (left_best_2)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize_3) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize_3)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best_2)) (PreH39 : ((0 : Int) <= left_best_2)) (PreH40 : (left_best_2 < (n_pre + 1))) (PreH41 : (lo <= left_best_2)) (PreH42 : (left_best_2 <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value_2 start lo (best - 1) left_best_2)) (PreH44 : (hi <= best)) (PreH45 : (right_best = (0 : Int))) (PreH46 : (right_value_2 = (0 : Int))) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH48 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l (0 : Int))) ∧ ((Znth idx_3 l (0 : Int)) <= 1000)))) (PreH49 : (has_right_2 ≠ (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out_3)
  ** (intArray.full heap_start_pre heap_cap starts_out_3)
  ** (intArray.full heap_lo_pre heap_cap los_out_3)
  ** (intArray.full heap_hi_pre heap_cap his_out_3)
  ** (intArray.full heap_best_pre heap_cap bests_out_3)
  ** ((( &( "has_left" ) )) # Int |-> (has_left_2))
  ** ((( &( "has_right" ) )) # Int |-> (has_right_2))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_3 + 1)))
  ** ((( &( "left_best" ) )) # Int |-> (left_best_2))
  ** ((( &( "left_value" ) )) # Int |-> (left_value_2))
  ** ((( &( "total" ) )) # Int64 |-> (total_3))
  ** ((( &( "right_value" ) )) # Int |-> (right_value_2))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
|--
  (EX vals_out : (List Int), EX starts_out : (List Int), EX los_out : (List Int), EX his_out : (List Int), EX bests_out : (List Int), EX slots_out : (List ((((Int × Int) × Int) × Int) × Int)), EX chosen : (List Int), EX total : Int, EX left_value : Int, EX left_best : Int, EX right_value : Int, EX hsize : Int, EX has_right : Int, EX has_left : Int, EX ans : Int, EX st_slots : (List Int),
  “ (has_left ≠ (0 : Int)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize + 1)) ” &&
  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l push_ps) ” &&
  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots))) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax push_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (RangeArgmax push_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ” &&
  “ (has_right ≠ (0 : Int)) ”
  &&  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots))
  ||
  (EX ans_2 : Int, EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX chosen_2 : (List Int), EX hsize_2 : Int, EX total_2 : Int, EX vals_out_2 : (List Int), EX starts_out_2 : (List Int), EX los_out_2 : (List Int), EX his_out_2 : (List Int), EX bests_out_2 : (List Int), EX slots_out_2 : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (RangeArgmax query_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out_2)) = heap_cap) ” &&
  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2) ” &&
  “ (NodeHeapState slots_out_2 (hsize_2 - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize_2 slots_out_2) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize_2) ” &&
  “ (hsize_2 <= heap_cap) ” &&
  “ ((hsize_2 + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total_2 (sublist ((0 : Int)) (hsize_2) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize_2) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> (((Znth right_best query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "has_right" ) )) # Int |-> (1))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out_2)
  ** (intArray.full heap_start_pre heap_cap starts_out_2)
  ** (intArray.full heap_lo_pre heap_cap los_out_2)
  ** (intArray.full heap_hi_pre heap_cap his_out_2)
  ** (intArray.full heap_best_pre heap_cap bests_out_2)
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_2 - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total_2 + value)))
  ** (intArray.full arr_pre n_pre l))

noncomputable def superPiano_entail_wit_11_3 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) (PreH52 : (has_right ≠ (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ (has_left ≠ (0 : Int)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize + 1)) ” &&
  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l push_ps) ” &&
  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots))) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax push_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (RangeArgmax push_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ” &&
  “ (has_right ≠ (0 : Int)) ”
  &&  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize + 1)))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_entail_wit_11_4 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize_2 : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out_2 : (List Int)) (starts_out_2 : (List Int)) (los_out_2 : (List Int)) (his_out_2 : (List Int)) (bests_out_2 : (List Int)) (slots_out_2 : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out_2)) = heap_cap)) (PreH10 : (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2)) (PreH11 : (NodeHeapState slots_out_2 (hsize_2 - 1))) (PreH12 : (FrontierPopTop pop_slots hsize_2 slots_out_2)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize_2)) (PreH35 : (hsize_2 <= heap_cap)) (PreH36 : ((hsize_2 + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize_2) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize_2)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out_2)
  ** (intArray.full heap_start_pre heap_cap starts_out_2)
  ** (intArray.full heap_lo_pre heap_cap los_out_2)
  ** (intArray.full heap_hi_pre heap_cap his_out_2)
  ** (intArray.full heap_best_pre heap_cap bests_out_2)
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_2 - 1)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps (best + 1) hi retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval) ” &&
  “ (retval <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out_2)) = heap_cap) ” &&
  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2) ” &&
  “ (NodeHeapState slots_out_2 (hsize_2 - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize_2 slots_out_2) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize_2) ” &&
  “ (hsize_2 <= heap_cap) ” &&
  “ ((hsize_2 + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize_2) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize_2) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out_2)
  ** (intArray.full heap_start_pre heap_cap starts_out_2)
  ** (intArray.full heap_lo_pre heap_cap los_out_2)
  ** (intArray.full heap_hi_pre heap_cap his_out_2)
  ** (intArray.full heap_best_pre heap_cap bests_out_2)
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_2 - 1)))
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_entail_wit_12_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (ans_2 : Int) (st_slots : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize_2 : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total_2 : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out_2 : (List Int)) (starts_out_2 : (List Int)) (los_out_2 : (List Int)) (his_out_2 : (List Int)) (bests_out_2 : (List Int)) (slots_out_2 : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out_2)) = heap_cap)) (PreH3 : (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2)) (PreH4 : (NodeHeapState slots_out_2 (hsize_2 + 1))) (PreH5 : (FrontierPushFields push_slots hsize_2 left_value start lo (best - 1) left_best slots_out_2)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize_2)) (PreH25 : (hsize_2 < heap_cap)) (PreH26 : (((hsize_2 + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total_2 ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize_2) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize_2)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH52 : (has_right ≠ (0 : Int))) (PreH53 : (has_left = (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out_2)
  ** (intArray.full heap_start_pre heap_cap starts_out_2)
  ** (intArray.full heap_lo_pre heap_cap los_out_2)
  ** (intArray.full heap_hi_pre heap_cap his_out_2)
  ** (intArray.full heap_best_pre heap_cap bests_out_2)
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize_2 + 1)))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total_2))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  EX ans : Int, EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX chosen : (List Int), EX hsize : Int, EX total : Int, EX vals_out : (List Int), EX starts_out : (List Int), EX los_out : (List Int), EX his_out : (List Int), EX bests_out : (List Int), EX slots_out : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (RangeArgmax query_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> (((Znth right_best query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "has_right" ) )) # Int |-> (1))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_entail_wit_12_2 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps (best + 1) hi retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval) ” &&
  “ (retval <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_entail_wit_13 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH52 : (has_right ≠ (0 : Int))) (PreH53 : (has_left ≠ (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ ((best + 1) <= hi) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ (hi <= n_pre) ” &&
  “ (RangeArgmax ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : ((best + 1) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH45 : ((0 : Int) <= right_best)) (PreH46 : (right_best < (n_pre + 1))) (PreH47 : ((best + 1) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH51 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH52 : (has_right ≠ (0 : Int))) (PreH53 : (has_left ≠ (0 : Int))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < (Zlength (slots_out))) ” &&
  “ (FrontierSplitState push_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (lo <= best) ” &&
  “ ((0 : Int) <= (best + 1)) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_14 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (1 = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < heap_cap) ” &&
  “ ((((hsize - 1) + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) (total + value) ((mkNode (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))) (start) ((best + 1)) (hi) (retval)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ ((best + 1) <= hi) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ (hi <= n_pre) ” &&
  “ (RangeArgmax ps (best + 1) hi retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval) ” &&
  “ (retval <= hi) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int))) start (best + 1) hi retval) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (SparseArgmaxBuilt query_ps query_st_slots ((Zlength (l)) + 1)) ” &&
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= (hsize - 1)) ” &&
  “ ((hsize - 1) < (Zlength (slots_out))) ” &&
  “ ((((hsize - 1) + 1) + (k_pre - t)) < (Zlength (slots_out))) ” &&
  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots)))) :: chosen) (t + 1) (total + (heap_top_value (pop_slots))) ((mkNode (((Znth retval query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int)))) ((heap_top_start (pop_slots))) (((heap_top_best (pop_slots)) + 1)) ((heap_top_hi (pop_slots))) (retval)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) ((hsize - 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize - 1)) ” &&
  “ ((0 : Int) <= ((heap_top_best (pop_slots)) + 1)) ” &&
  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval query_ps (0 : Int)) - (Znth ((heap_top_start (pop_slots)) - 1) query_ps (0 : Int))) (heap_top_start (pop_slots)) ((heap_top_best (pop_slots)) + 1) (heap_top_hi (pop_slots)) retval) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_15_1 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH27 : (NodeHeapState right_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1) <= hi)) (PreH35 : ((0 : Int) <= (best + 1))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH38 : ((0 : Int) <= right_best)) (PreH39 : (right_best < (n_pre + 1))) (PreH40 : ((best + 1) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH43 : ((0 : Int) <= lo)) (PreH44 : (lo <= (best - 1))) (PreH45 : ((best - 1) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH47 : ((0 : Int) <= left_best)) (PreH48 : (left_best < (n_pre + 1))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH53 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= has_left) ” &&
  “ (has_left <= 1) ” &&
  “ ((0 : Int) <= has_right) ” &&
  “ (has_right <= 1) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ (INT_MIN <= left_value) ” &&
  “ (left_value <= INT_MAX) ” &&
  “ (INT_MIN <= right_value) ” &&
  “ (right_value <= INT_MAX) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t)) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH27 : (NodeHeapState right_slots hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : ((0 : Int) <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1) <= hi)) (PreH35 : ((0 : Int) <= (best + 1))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH38 : ((0 : Int) <= right_best)) (PreH39 : (right_best < (n_pre + 1))) (PreH40 : ((best + 1) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH43 : ((0 : Int) <= lo)) (PreH44 : (lo <= (best - 1))) (PreH45 : ((best - 1) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH47 : ((0 : Int) <= left_best)) (PreH48 : (left_best < (n_pre + 1))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH53 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= 1) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= 1) ” &&
  “ (INT_MIN <= left_value) ” &&
  “ (left_value <= INT_MAX) ” &&
  “ (INT_MIN <= right_value) ” &&
  “ (right_value <= INT_MAX) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < (Zlength (slots_out))) ” &&
  “ (((hsize + 1) + (k_pre - (t + 1))) < (Zlength (slots_out))) ” &&
  “ (FrontierState right_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (best <= hi) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_15_2 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = (0 : Int))) (PreH20 : (left_best = (0 : Int))) (PreH21 : (left_value = (0 : Int))) (PreH22 : (has_right = 1)) (PreH23 : ((0 : Int) <= t)) (PreH24 : (t < k_pre)) (PreH25 : ((0 : Int) <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH29 : (NodeHeapState right_slots hsize)) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : ((0 : Int) <= (start - 1))) (PreH33 : ((start - 1) < (n_pre + 1))) (PreH34 : ((0 : Int) <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1) <= hi)) (PreH37 : ((0 : Int) <= (best + 1))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= has_left) ” &&
  “ (has_left <= 1) ” &&
  “ ((0 : Int) <= has_right) ” &&
  “ (has_right <= 1) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ (INT_MIN <= left_value) ” &&
  “ (left_value <= INT_MAX) ” &&
  “ (INT_MIN <= right_value) ” &&
  “ (right_value <= INT_MAX) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH3 : (NodeHeapState slots_out (hsize + 1))) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1) hi right_best slots_out)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps)) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2)) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH19 : (has_left = (0 : Int))) (PreH20 : (left_best = (0 : Int))) (PreH21 : (left_value = (0 : Int))) (PreH22 : (has_right = 1)) (PreH23 : ((0 : Int) <= t)) (PreH24 : (t < k_pre)) (PreH25 : ((0 : Int) <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH29 : (NodeHeapState right_slots hsize)) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : ((0 : Int) <= (start - 1))) (PreH33 : ((start - 1) < (n_pre + 1))) (PreH34 : ((0 : Int) <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1) <= hi)) (PreH37 : ((0 : Int) <= (best + 1))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= 1) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < ((Zlength (l)) + 1)) ” &&
  “ (INT_MIN <= (0 : Int)) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ (INT_MIN <= right_value) ” &&
  “ (right_value <= INT_MAX) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < (Zlength (slots_out))) ” &&
  “ (((hsize + 1) + (k_pre - (t + 1))) < (Zlength (slots_out))) ” &&
  “ (FrontierState right_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ (best <= hi) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_15_3 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (left_best : Int) (left_value : Int) (right_best : Int) (right_value : Int) (t : Int) (hsize : Int) (total : Int) (best : Int) (start : Int) (lo : Int) (hi : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2)) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (has_right = (0 : Int))) (PreH17 : (left_best = (0 : Int))) (PreH18 : (left_value = (0 : Int))) (PreH19 : (right_best = (0 : Int))) (PreH20 : (right_value = (0 : Int))) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1))) < heap_cap)) (PreH26 : (FrontierSplitState ps_2 n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH27 : (NodeHeapState slots_2 hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best)) (PreH35 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH36 : (has_right = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
  ** (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= has_left) ” &&
  “ (has_left <= 1) ” &&
  “ ((0 : Int) <= has_right) ” &&
  “ (has_right <= 1) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ (INT_MIN <= left_value) ” &&
  “ (left_value <= INT_MAX) ” &&
  “ (INT_MIN <= right_value) ” &&
  “ (right_value <= INT_MAX) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((hsize + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (left_best : Int) (left_value : Int) (right_best : Int) (right_value : Int) (t : Int) (hsize : Int) (total : Int) (best : Int) (start : Int) (lo : Int) (hi : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2)) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (has_right = (0 : Int))) (PreH17 : (left_best = (0 : Int))) (PreH18 : (left_value = (0 : Int))) (PreH19 : (right_best = (0 : Int))) (PreH20 : (right_value = (0 : Int))) (PreH21 : ((0 : Int) <= t)) (PreH22 : (t < k_pre)) (PreH23 : ((0 : Int) <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1))) < heap_cap)) (PreH26 : (FrontierSplitState ps_2 n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total (@List.nil ((((Int × Int) × Int) × Int) × Int)) (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH27 : (NodeHeapState slots_2 hsize)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best)) (PreH35 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH36 : (has_right = (0 : Int))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < ((Zlength (l)) + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < ((Zlength (l)) + 1)) ” &&
  “ (INT_MIN <= (0 : Int)) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ (INT_MIN <= (0 : Int)) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) (start) (hi)) :: chosen) (t + 1) total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (((start + L_pre) - 1) <= hi) ” &&
  “ ((0 : Int) <= hi) ” &&
  “ (hi <= hi) ” &&
  “ (hi <= hi) ” &&
  “ (hi <= (Zlength (l))) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_15_4 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = (0 : Int))) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (hi <= best)) (PreH45 : (right_best = (0 : Int))) (PreH46 : (right_value = (0 : Int))) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH48 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH49 : (has_right = (0 : Int))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= has_left) ” &&
  “ (has_left <= 1) ” &&
  “ ((0 : Int) <= has_right) ” &&
  “ (has_right <= 1) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ (INT_MIN <= left_value) ” &&
  “ (left_value <= INT_MAX) ” &&
  “ (INT_MIN <= right_value) ” &&
  “ (right_value <= INT_MAX) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (has_left ≠ (0 : Int))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize + 1))) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1) left_best slots_out)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps)) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2)) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH20 : (has_left = 1)) (PreH21 : (has_right = (0 : Int))) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t < k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH28 : (NodeHeapState push_slots hsize)) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : ((0 : Int) <= (start - 1))) (PreH32 : ((start - 1) < (n_pre + 1))) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= (best - 1))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH39 : ((0 : Int) <= left_best)) (PreH40 : (left_best < (n_pre + 1))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH44 : (hi <= best)) (PreH45 : (right_best = (0 : Int))) (PreH46 : (right_value = (0 : Int))) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH48 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) (PreH49 : (has_right = (0 : Int))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” &&
  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= 1) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < ((Zlength (l)) + 1)) ” &&
  “ (INT_MIN <= left_value) ” &&
  “ (left_value <= INT_MAX) ” &&
  “ (INT_MIN <= (0 : Int)) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) <= (hsize + 1)) ” &&
  “ ((hsize + 1) < (Zlength (slots_out))) ” &&
  “ (((hsize + 1) + (k_pre - (t + 1))) < (Zlength (slots_out))) ” &&
  “ (FrontierState push_ps (Zlength (l)) L_pre R_pre ((ChordCode ((Zlength (l))) (start) (best)) :: chosen) (t + 1) total (sublist ((0 : Int)) ((hsize + 1)) (slots))) ” &&
  “ (NodeHeapState slots (hsize + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ (lo <= best) ”
  &&  emp
)

noncomputable def superPiano_entail_wit_16 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (left_best : Int) (right_best : Int) (left_value : Int) (right_value : Int) (t : Int) (hsize : Int) (total : Int) (best : Int) (start : Int) (hi : Int) (lo : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2)) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH15 : ((0 : Int) <= has_left)) (PreH16 : (has_left <= 1)) (PreH17 : ((0 : Int) <= has_right)) (PreH18 : (has_right <= 1)) (PreH19 : ((0 : Int) <= left_best)) (PreH20 : (left_best < (n_pre + 1))) (PreH21 : ((0 : Int) <= right_best)) (PreH22 : (right_best < (n_pre + 1))) (PreH23 : (INT_MIN <= left_value)) (PreH24 : (left_value <= INT_MAX)) (PreH25 : (INT_MIN <= right_value)) (PreH26 : (right_value <= INT_MAX)) (PreH27 : ((0 : Int) <= t)) (PreH28 : (t < k_pre)) (PreH29 : ((0 : Int) <= hsize)) (PreH30 : (hsize < heap_cap)) (PreH31 : ((hsize + (k_pre - (t + 1))) < heap_cap)) (PreH32 : (FrontierState ps_2 n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH33 : (NodeHeapState slots_2 hsize)) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best)) (PreH35 : (1 <= start)) (PreH36 : (start <= n_pre)) (PreH37 : ((0 : Int) <= (start - 1))) (PreH38 : ((start - 1) < (n_pre + 1))) (PreH39 : (((start + L_pre) - 1) <= lo)) (PreH40 : ((0 : Int) <= lo)) (PreH41 : (lo <= best)) (PreH42 : (best <= hi)) (PreH43 : (hi <= n_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
  ** (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
|--
  EX chosen : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ans : Int, EX st_slots : (List Int), EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= (t + 1)) ” &&
  “ ((t + 1) <= k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - (t + 1))) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen (t + 1) total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (((t + 1) < k_pre) -> ((0 : Int) < hsize)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
) \/
(
forall (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans_2 : Int) (st_slots_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (chosen_2 : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (left_best : Int) (right_best : Int) (left_value : Int) (right_value : Int) (t : Int) (hsize : Int) (total : Int) (best : Int) (start : Int) (hi : Int) (lo : Int) (value : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2)) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2)) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH15 : ((0 : Int) <= has_left)) (PreH16 : (has_left <= 1)) (PreH17 : ((0 : Int) <= has_right)) (PreH18 : (has_right <= 1)) (PreH19 : ((0 : Int) <= left_best)) (PreH20 : (left_best < (n_pre + 1))) (PreH21 : ((0 : Int) <= right_best)) (PreH22 : (right_best < (n_pre + 1))) (PreH23 : (INT_MIN <= left_value)) (PreH24 : (left_value <= INT_MAX)) (PreH25 : (INT_MIN <= right_value)) (PreH26 : (right_value <= INT_MAX)) (PreH27 : ((0 : Int) <= t)) (PreH28 : (t < k_pre)) (PreH29 : ((0 : Int) <= hsize)) (PreH30 : (hsize < heap_cap)) (PreH31 : ((hsize + (k_pre - (t + 1))) < heap_cap)) (PreH32 : (FrontierState ps_2 n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH33 : (NodeHeapState slots_2 hsize)) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best)) (PreH35 : (1 <= start)) (PreH36 : (start <= n_pre)) (PreH37 : ((0 : Int) <= (start - 1))) (PreH38 : ((start - 1) < (n_pre + 1))) (PreH39 : (((start + L_pre) - 1) <= lo)) (PreH40 : ((0 : Int) <= lo)) (PreH41 : (lo <= best)) (PreH42 : (best <= hi)) (PreH43 : (hi <= n_pre)) (PreH44 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  TT && emp 
|--
  EX chosen : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2) ” &&
  “ ((0 : Int) <= (t + 1)) ” &&
  “ ((t + 1) <= k_pre) ” &&
  “ (hsize <= (((Zlength (l)) + k_pre) + 1)) ” &&
  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre chosen (t + 1) total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (((t + 1) < k_pre) -> ((0 : Int) < hsize)) ”
  &&  emp
)

noncomputable def superPiano_return_wit_1 : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (chosen : (List Int)) (total : Int) (hsize : Int) (t : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (ans : Int) (st_slots_2 : (List Int)) (ps_2 : (List Int)) (heap_cap : Int) (PreH1 : (t >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre) + 1) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2)) (PreH12 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans)) (PreH14 : ((Zlength (slots_2)) = heap_cap)) (PreH15 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH16 : ((0 : Int) <= t)) (PreH17 : (t <= k_pre)) (PreH18 : ((0 : Int) <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t)) < heap_cap)) (PreH21 : (FrontierState ps_2 n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH22 : (NodeHeapState slots_2 hsize)) (PreH23 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH24 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps_2)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots_2)
  ** (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
|--
  EX st_slots : (List Int), EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)), EX ps : (List Int),
  “ (PrefixSums l ps) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre total) ” &&
  “ ((Zlength (slots)) = ((n_pre + k_pre) + 1)) ” &&
  “ (NodeArrays slots vals starts los his bests) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre ((n_pre + k_pre) + 1) vals)
  ** (intArray.full heap_start_pre ((n_pre + k_pre) + 1) starts)
  ** (intArray.full heap_lo_pre ((n_pre + k_pre) + 1) los)
  ** (intArray.full heap_hi_pre ((n_pre + k_pre) + 1) his)
  ** (intArray.full heap_best_pre ((n_pre + k_pre) + 1) bests)
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (l : (List Int)) (chosen : (List Int)) (total : Int) (hsize : Int) (t : Int) (vals_2 : (List Int)) (starts_2 : (List Int)) (los_2 : (List Int)) (his_2 : (List Int)) (bests_2 : (List Int)) (slots_2 : (List ((((Int × Int) × Int) × Int) × Int))) (ans : Int) (st_slots_2 : (List Int)) (ps_2 : (List Int)) (heap_cap : Int) (PreH1 : (t >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre) + 1) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2)) (PreH12 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1))) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans)) (PreH14 : ((Zlength (slots_2)) = heap_cap)) (PreH15 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2)) (PreH16 : ((0 : Int) <= t)) (PreH17 : (t <= k_pre)) (PreH18 : ((0 : Int) <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t)) < heap_cap)) (PreH21 : (FrontierState ps_2 n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots_2)))) (PreH22 : (NodeHeapState slots_2 hsize)) (PreH23 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH24 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_2)
  ** (intArray.full heap_start_pre heap_cap starts_2)
  ** (intArray.full heap_lo_pre heap_cap los_2)
  ** (intArray.full heap_hi_pre heap_cap his_2)
  ** (intArray.full heap_best_pre heap_cap bests_2)
|--
  EX vals : (List Int), EX starts : (List Int), EX los : (List Int), EX his : (List Int), EX bests : (List Int), EX slots : (List ((((Int × Int) × Int) × Int) × Int)),
  “ (PrefixSums l ps_2) ” &&
  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre total) ” &&
  “ ((Zlength (slots)) = ((n_pre + k_pre) + 1)) ” &&
  “ (NodeArrays slots vals starts los his bests) ”
  &&  (intArray.full heap_value_pre ((n_pre + k_pre) + 1) vals)
  ** (intArray.full heap_start_pre ((n_pre + k_pre) + 1) starts)
  ** (intArray.full heap_lo_pre ((n_pre + k_pre) + 1) los)
  ** (intArray.full heap_hi_pre ((n_pre + k_pre) + 1) his)
  ** (intArray.full heap_best_pre ((n_pre + k_pre) + 1) bests)
)

noncomputable def superPiano_partial_solve_wit_1_pure : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps_2)) (PreH10 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans)) (PreH12 : ((-9223372036854775808) <= ans)) (PreH13 : (ans <= 9223372036854775807)) (PreH14 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int |-> (((n_pre + k_pre) + 1)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
|--
  EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < ((Zlength (l)) + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (PrefixSums l ps) ”
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans : Int) (PreH1 : (R_pre <= INT_MAX)) (PreH2 : (L_pre <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((n_pre + k_pre) + 1) <= INT_MAX)) (PreH6 : (R_pre >= INT_MIN)) (PreH7 : (L_pre >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((n_pre + k_pre) + 1) >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps_2)) (PreH20 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH21 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans)) (PreH22 : ((-9223372036854775808) <= ans)) (PreH23 : (ans <= 9223372036854775807)) (PreH24 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int |-> (((n_pre + k_pre) + 1)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
|--
  EX ps : (List Int),
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < ((Zlength (l)) + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < ((Zlength (l)) + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (PrefixSums l ps) ”
)

noncomputable def superPiano_partial_solve_wit_1_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps_2 : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps_2)) (PreH10 : forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans)) (PreH12 : ((-9223372036854775808) <= ans)) (PreH13 : (ans <= 9223372036854775807)) (PreH14 : forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))
|--
  EX ps : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < ((Zlength (l)) + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (PrefixSums l ps) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps_2) ” &&
  “ forall (idx_3 : Int) , ((((0 : Int) <= idx_3) ∧ (idx_3 < (n_pre + 1))) -> ((INT_MIN <= (Znth idx_3 ps_2 (0 : Int))) ∧ ((Znth idx_3 ps_2 (0 : Int)) <= INT_MAX))) ” &&
  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans) ” &&
  “ ((-9223372036854775808) <= ans) ” &&
  “ (ans <= 9223372036854775807) ” &&
  “ forall (idx_4 : Int) , ((((0 : Int) <= idx_4) ∧ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l (0 : Int))) ∧ ((Znth idx_4 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full prefix_pre (n_pre + 1))
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_start_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_lo_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_hi_pre ((n_pre + k_pre) + 1))
  ** (intArray.undef_full heap_best_pre ((n_pre + k_pre) + 1))

noncomputable def superPiano_partial_solve_wit_1 : Prop := superPiano_partial_solve_wit_1_pure -> superPiano_partial_solve_wit_1_aux

noncomputable def superPiano_partial_solve_wit_2_pure : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (heap_cap : Int) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS))) (PreH12 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS)) ” &&
  “ ((Zlength (ps)) = (n_pre + 1)) ”
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (heap_cap : Int) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps)) (PreH21 : ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS))) (PreH22 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH24 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ ((Zlength (ps)) = (n_pre + 1)) ”
)

noncomputable def superPiano_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (heap_cap : Int) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps)) (PreH21 : ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS))) (PreH22 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH24 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ ((Zlength (ps)) = (n_pre + 1)) ”

noncomputable def superPiano_partial_solve_wit_2_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (heap_cap : Int) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS))) (PreH12 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS)) ” &&
  “ ((Zlength (ps)) = (n_pre + 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ ((Zlength (st_slots)) = ((n_pre + 1) * ST_LEVELS)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.undef_full st_pre ((n_pre + 1) * ST_LEVELS))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)

noncomputable def superPiano_partial_solve_wit_2 : Prop := superPiano_partial_solve_wit_2_pure -> superPiano_partial_solve_wit_2_aux

noncomputable def superPiano_partial_solve_wit_3_pure : Prop :=
  (
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (heap_cap : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "hsize" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (((n_pre - L_pre) + 1) <= heap_cap) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ ((Zlength (ps)) = (n_pre + 1)) ”
) \/
(
forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (heap_cap : Int) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH22 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH24 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "hsize" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ ((Zlength (ps)) = (n_pre + 1)) ”
)

noncomputable def superPiano_partial_solve_wit_3_pure_split_goal_1 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (heap_cap : Int) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH22 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH24 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  ((( &( "hsize" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ ((Zlength (ps)) = (n_pre + 1)) ”

noncomputable def superPiano_partial_solve_wit_3_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (heap_cap : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps)) (PreH11 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX)))) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (((n_pre - L_pre) + 1) <= heap_cap) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ ((Zlength (ps)) = (n_pre + 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (n_pre + 1))) -> ((INT_MIN <= (Znth idx ps (0 : Int))) ∧ ((Znth idx ps (0 : Int)) <= INT_MAX))) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.undef_full heap_value_pre heap_cap)
  ** (intArray.undef_full heap_start_pre heap_cap)
  ** (intArray.undef_full heap_lo_pre heap_cap)
  ** (intArray.undef_full heap_hi_pre heap_cap)
  ** (intArray.undef_full heap_best_pre heap_cap)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_3 : Prop := superPiano_partial_solve_wit_3_pure -> superPiano_partial_solve_wit_3_aux

noncomputable def superPiano_partial_solve_wit_4_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (PreH1 : (t < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre) + 1) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps)) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : ((Zlength (slots)) = heap_cap)) (PreH15 : (NodeArrays slots vals starts los his bests)) (PreH16 : ((0 : Int) <= t)) (PreH17 : (t <= k_pre)) (PreH18 : ((0 : Int) <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t)) < heap_cap)) (PreH21 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH22 : (NodeHeapState slots hsize)) (PreH23 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH24 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ”

noncomputable def superPiano_partial_solve_wit_4_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (PreH1 : (t < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre) + 1) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps)) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH14 : ((Zlength (slots)) = heap_cap)) (PreH15 : (NodeArrays slots vals starts los his bests)) (PreH16 : ((0 : Int) <= t)) (PreH17 : (t <= k_pre)) (PreH18 : ((0 : Int) <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t)) < heap_cap)) (PreH21 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH22 : (NodeHeapState slots hsize)) (PreH23 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH24 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (t < k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t <= k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ ((t < k_pre) -> ((0 : Int) < hsize)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_4 : Prop := superPiano_partial_solve_wit_4_pure -> superPiano_partial_solve_wit_4_aux

noncomputable def superPiano_partial_solve_wit_5_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (PreH1 : (retval = (heap_top_value (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (t < k_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l ps)) (PreH15 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (slots)) = heap_cap)) (PreH18 : (NodeArrays slots vals starts los his bests)) (PreH19 : ((0 : Int) <= t)) (PreH20 : (t <= k_pre)) (PreH21 : ((0 : Int) <= hsize)) (PreH22 : (hsize <= heap_cap)) (PreH23 : ((hsize + (k_pre - t)) < heap_cap)) (PreH24 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH25 : (NodeHeapState slots hsize)) (PreH26 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "start" ) )) # Int |->_)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** ((( &( "value" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ”

noncomputable def superPiano_partial_solve_wit_5_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (PreH1 : (retval = (heap_top_value (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (t < k_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre) + 1) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l ps)) (PreH15 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH16 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH17 : ((Zlength (slots)) = heap_cap)) (PreH18 : (NodeArrays slots vals starts los his bests)) (PreH19 : ((0 : Int) <= t)) (PreH20 : (t <= k_pre)) (PreH21 : ((0 : Int) <= hsize)) (PreH22 : (hsize <= heap_cap)) (PreH23 : ((hsize + (k_pre - t)) < heap_cap)) (PreH24 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH25 : (NodeHeapState slots hsize)) (PreH26 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval = (heap_top_value (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (t < k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t <= k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ ((t < k_pre) -> ((0 : Int) < hsize)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_5 : Prop := superPiano_partial_solve_wit_5_pure -> superPiano_partial_solve_wit_5_aux

noncomputable def superPiano_partial_solve_wit_6_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (heap_top_start (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (retval = (heap_top_value (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests)) (PreH6 : (NodeHeapState slots hsize)) (PreH7 : (t < k_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (1 <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (((n_pre + k_pre) + 1) <= 200000)) (PreH15 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (PrefixSums l ps)) (PreH18 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH19 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH20 : ((Zlength (slots)) = heap_cap)) (PreH21 : (NodeArrays slots vals starts los his bests)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t <= k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize <= heap_cap)) (PreH26 : ((hsize + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH28 : (NodeHeapState slots hsize)) (PreH29 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "lo" ) )) # Int |->_)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** ((( &( "start" ) )) # Int |-> (retval_2))
  ** ((( &( "value" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ”

noncomputable def superPiano_partial_solve_wit_6_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (heap_top_start (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (retval = (heap_top_value (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests)) (PreH6 : (NodeHeapState slots hsize)) (PreH7 : (t < k_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (1 <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (((n_pre + k_pre) + 1) <= 200000)) (PreH15 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (PrefixSums l ps)) (PreH18 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH19 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH20 : ((Zlength (slots)) = heap_cap)) (PreH21 : (NodeArrays slots vals starts los his bests)) (PreH22 : ((0 : Int) <= t)) (PreH23 : (t <= k_pre)) (PreH24 : ((0 : Int) <= hsize)) (PreH25 : (hsize <= heap_cap)) (PreH26 : ((hsize + (k_pre - t)) < heap_cap)) (PreH27 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH28 : (NodeHeapState slots hsize)) (PreH29 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval_2 = (heap_top_start (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval = (heap_top_value (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (t < k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t <= k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ ((t < k_pre) -> ((0 : Int) < hsize)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_6 : Prop := superPiano_partial_solve_wit_6_pure -> superPiano_partial_solve_wit_6_aux

noncomputable def superPiano_partial_solve_wit_7_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (heap_top_lo (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (retval_2 = (heap_top_start (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests)) (PreH6 : (NodeHeapState slots hsize)) (PreH7 : (retval = (heap_top_value (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests)) (PreH9 : (NodeHeapState slots hsize)) (PreH10 : (t < k_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps)) (PreH21 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (slots)) = heap_cap)) (PreH24 : (NodeArrays slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t <= k_pre)) (PreH27 : ((0 : Int) <= hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH31 : (NodeHeapState slots hsize)) (PreH32 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH33 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "hi" ) )) # Int |->_)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** ((( &( "lo" ) )) # Int |-> (retval_3))
  ** ((( &( "start" ) )) # Int |-> (retval_2))
  ** ((( &( "value" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ”

noncomputable def superPiano_partial_solve_wit_7_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (heap_top_lo (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (retval_2 = (heap_top_start (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests)) (PreH6 : (NodeHeapState slots hsize)) (PreH7 : (retval = (heap_top_value (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests)) (PreH9 : (NodeHeapState slots hsize)) (PreH10 : (t < k_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps)) (PreH21 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (slots)) = heap_cap)) (PreH24 : (NodeArrays slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t <= k_pre)) (PreH27 : ((0 : Int) <= hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH31 : (NodeHeapState slots hsize)) (PreH32 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH33 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval_3 = (heap_top_lo (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval_2 = (heap_top_start (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval = (heap_top_value (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (t < k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t <= k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ ((t < k_pre) -> ((0 : Int) < hsize)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_7 : Prop := superPiano_partial_solve_wit_7_pure -> superPiano_partial_solve_wit_7_aux

noncomputable def superPiano_partial_solve_wit_8_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (retval_2 : Int) (retval_3 : Int) (retval_4 : Int) (PreH1 : (retval_4 = (heap_top_hi (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (retval_3 = (heap_top_lo (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests)) (PreH6 : (NodeHeapState slots hsize)) (PreH7 : (retval_2 = (heap_top_start (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests)) (PreH9 : (NodeHeapState slots hsize)) (PreH10 : (retval = (heap_top_value (slots)))) (PreH11 : (NodeArrays slots vals starts los his bests)) (PreH12 : (NodeHeapState slots hsize)) (PreH13 : (t < k_pre)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (1 <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= n_pre)) (PreH19 : (1 <= k_pre)) (PreH20 : (((n_pre + k_pre) + 1) <= 200000)) (PreH21 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (PrefixSums l ps)) (PreH24 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH25 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH26 : ((Zlength (slots)) = heap_cap)) (PreH27 : (NodeArrays slots vals starts los his bests)) (PreH28 : ((0 : Int) <= t)) (PreH29 : (t <= k_pre)) (PreH30 : ((0 : Int) <= hsize)) (PreH31 : (hsize <= heap_cap)) (PreH32 : ((hsize + (k_pre - t)) < heap_cap)) (PreH33 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH34 : (NodeHeapState slots hsize)) (PreH35 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH36 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "best" ) )) # Int |->_)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** ((( &( "hi" ) )) # Int |-> (retval_4))
  ** ((( &( "lo" ) )) # Int |-> (retval_3))
  ** ((( &( "start" ) )) # Int |-> (retval_2))
  ** ((( &( "value" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ”

noncomputable def superPiano_partial_solve_wit_8_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (total : Int) (hsize : Int) (t : Int) (ans : Int) (st_slots : (List Int)) (ps : (List Int)) (heap_cap : Int) (slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (retval : Int) (retval_2 : Int) (retval_3 : Int) (retval_4 : Int) (PreH1 : (retval_4 = (heap_top_hi (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests)) (PreH3 : (NodeHeapState slots hsize)) (PreH4 : (retval_3 = (heap_top_lo (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests)) (PreH6 : (NodeHeapState slots hsize)) (PreH7 : (retval_2 = (heap_top_start (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests)) (PreH9 : (NodeHeapState slots hsize)) (PreH10 : (retval = (heap_top_value (slots)))) (PreH11 : (NodeArrays slots vals starts los his bests)) (PreH12 : (NodeHeapState slots hsize)) (PreH13 : (t < k_pre)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (1 <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= n_pre)) (PreH19 : (1 <= k_pre)) (PreH20 : (((n_pre + k_pre) + 1) <= 200000)) (PreH21 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (PrefixSums l ps)) (PreH24 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH25 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH26 : ((Zlength (slots)) = heap_cap)) (PreH27 : (NodeArrays slots vals starts los his bests)) (PreH28 : ((0 : Int) <= t)) (PreH29 : (t <= k_pre)) (PreH30 : ((0 : Int) <= hsize)) (PreH31 : (hsize <= heap_cap)) (PreH32 : ((hsize + (k_pre - t)) < heap_cap)) (PreH33 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots)))) (PreH34 : (NodeHeapState slots hsize)) (PreH35 : ((t < k_pre) -> ((0 : Int) < hsize))) (PreH36 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval_4 = (heap_top_hi (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval_3 = (heap_top_lo (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval_2 = (heap_top_start (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (retval = (heap_top_value (slots))) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ (t < k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (slots)) = heap_cap) ” &&
  “ (NodeArrays slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t <= k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (slots))) ” &&
  “ (NodeHeapState slots hsize) ” &&
  “ ((t < k_pre) -> ((0 : Int) < hsize)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_8 : Prop := superPiano_partial_solve_wit_8_pure -> superPiano_partial_solve_wit_8_aux

noncomputable def superPiano_partial_solve_wit_9_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (value = (heap_top_value (pop_slots)))) (PreH2 : (start = (heap_top_start (pop_slots)))) (PreH3 : (lo = (heap_top_lo (pop_slots)))) (PreH4 : (hi = (heap_top_hi (pop_slots)))) (PreH5 : (best = (heap_top_best (pop_slots)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps)) (PreH16 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (pop_slots)) = heap_cap)) (PreH19 : (NodeArrays pop_slots vals starts los his bests)) (PreH20 : ((0 : Int) <= t)) (PreH21 : (t < k_pre)) (PreH22 : ((0 : Int) < hsize)) (PreH23 : (hsize <= heap_cap)) (PreH24 : ((hsize + (k_pre - t)) < heap_cap)) (PreH25 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH26 : (NodeHeapState pop_slots hsize)) (PreH27 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : (((start + L_pre) - 1) <= lo)) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= best)) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ (NodeHeapState pop_slots hsize) ”

noncomputable def superPiano_partial_solve_wit_9_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ps : (List Int)) (ans : Int) (st_slots : (List Int)) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (PreH1 : (value = (heap_top_value (pop_slots)))) (PreH2 : (start = (heap_top_start (pop_slots)))) (PreH3 : (lo = (heap_top_lo (pop_slots)))) (PreH4 : (hi = (heap_top_hi (pop_slots)))) (PreH5 : (best = (heap_top_best (pop_slots)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre) + 1) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps)) (PreH16 : (SparseArgmaxBuilt ps st_slots (n_pre + 1))) (PreH17 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans)) (PreH18 : ((Zlength (pop_slots)) = heap_cap)) (PreH19 : (NodeArrays pop_slots vals starts los his bests)) (PreH20 : ((0 : Int) <= t)) (PreH21 : (t < k_pre)) (PreH22 : ((0 : Int) < hsize)) (PreH23 : (hsize <= heap_cap)) (PreH24 : ((hsize + (k_pre - t)) < heap_cap)) (PreH25 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH26 : (NodeHeapState pop_slots hsize)) (PreH27 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best)) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : ((0 : Int) <= (start - 1))) (PreH31 : ((start - 1) < (n_pre + 1))) (PreH32 : (((start + L_pre) - 1) <= lo)) (PreH33 : ((0 : Int) <= lo)) (PreH34 : (lo <= best)) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
|--
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l ps) ” &&
  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap vals)
  ** (intArray.full heap_start_pre heap_cap starts)
  ** (intArray.full heap_lo_pre heap_cap los)
  ** (intArray.full heap_hi_pre heap_cap his)
  ** (intArray.full heap_best_pre heap_cap bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_9 : Prop := superPiano_partial_solve_wit_9_pure -> superPiano_partial_solve_wit_9_aux

noncomputable def superPiano_partial_solve_wit_10_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo <= (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best - 1) < (n_pre + 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ”

noncomputable def superPiano_partial_solve_wit_10_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : (lo <= (best - 1))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH4 : (NodeHeapState slots_out (hsize - 1))) (PreH5 : (FrontierPopTop pop_slots hsize slots_out)) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre) + 1) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps)) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests)) (PreH25 : ((0 : Int) <= t)) (PreH26 : (t < k_pre)) (PreH27 : ((0 : Int) < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t)) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH31 : (NodeHeapState pop_slots hsize)) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : ((0 : Int) <= (start - 1))) (PreH36 : ((start - 1) < (n_pre + 1))) (PreH37 : (((start + L_pre) - 1) <= lo)) (PreH38 : ((0 : Int) <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best - 1) < (n_pre + 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_10 : Prop := superPiano_partial_solve_wit_10_pure -> superPiano_partial_solve_wit_10_aux

noncomputable def superPiano_partial_solve_wit_11 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps lo (best - 1) retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ (lo <= retval) ” &&
  “ (retval <= (best - 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((prefix_pre + (retval * sizeof(INT)))) # Int |-> ((Znth retval query_ps (0 : Int))))
  ** (intArray.missing_i prefix_pre retval (0 : Int) (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_12 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : (lo <= (best - 1))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH10 : (NodeHeapState slots_out (hsize - 1))) (PreH11 : (FrontierPopTop pop_slots hsize slots_out)) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre) + 1) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps)) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests)) (PreH31 : ((0 : Int) <= t)) (PreH32 : (t < k_pre)) (PreH33 : ((0 : Int) < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t)) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH37 : (NodeHeapState pop_slots hsize)) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : ((0 : Int) <= (start - 1))) (PreH42 : ((start - 1) < (n_pre + 1))) (PreH43 : (((start + L_pre) - 1) <= lo)) (PreH44 : ((0 : Int) <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps lo (best - 1) retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ (lo <= retval) ” &&
  “ (retval <= (best - 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1) * sizeof(INT)))) # Int |-> ((Znth (start - 1) query_ps (0 : Int))))
  ** (intArray.missing_i prefix_pre (start - 1) (0 : Int) (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_13_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> (((Znth retval query_ps (0 : Int)) - (Znth (start - 1) query_ps (0 : Int)))))
  ** ((( &( "left_best" ) )) # Int |-> (retval))
  ** ((( &( "has_left" ) )) # Int |-> (1))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi < (n_pre + 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ”

noncomputable def superPiano_partial_solve_wit_13_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : ((best + 1) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < (n_pre + 1))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH8 : (lo <= (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi < (n_pre + 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (RangeArgmax query_ps lo (best - 1) retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ (lo <= retval) ” &&
  “ (retval <= (best - 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_13 : Prop := superPiano_partial_solve_wit_13_pure -> superPiano_partial_solve_wit_13_aux

noncomputable def superPiano_partial_solve_wit_14_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) <= hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "right_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_right" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_value" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "left_best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "has_left" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> ((hsize - 1)))
  ** ((( &( "total" ) )) # Int64 |-> ((total + value)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi < (n_pre + 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ”

noncomputable def superPiano_partial_solve_wit_14_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (PreH1 : ((best + 1) <= hi)) (PreH2 : (lo > (best - 1))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH5 : (NodeHeapState slots_out (hsize - 1))) (PreH6 : (FrontierPopTop pop_slots hsize slots_out)) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre) + 1) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps)) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests)) (PreH26 : ((0 : Int) <= t)) (PreH27 : (t < k_pre)) (PreH28 : ((0 : Int) < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t)) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH32 : (NodeHeapState pop_slots hsize)) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : ((0 : Int) <= (start - 1))) (PreH37 : ((start - 1) < (n_pre + 1))) (PreH38 : (((start + L_pre) - 1) <= lo)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
|--
  “ (1 <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) <= 100001) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi < (n_pre + 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_14 : Prop := superPiano_partial_solve_wit_14_pure -> superPiano_partial_solve_wit_14_aux

noncomputable def superPiano_partial_solve_wit_15 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval_2)) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1))) (PreH4 : ((best + 1) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH9 : ((0 : Int) <= retval)) (PreH10 : (retval < (n_pre + 1))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps (best + 1) hi retval_2) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval_2) ” &&
  “ (retval_2 <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (RangeArgmax query_ps lo (best - 1) retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ (lo <= retval) ” &&
  “ (retval <= (best - 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((prefix_pre + (retval_2 * sizeof(INT)))) # Int |-> ((Znth retval_2 query_ps (0 : Int))))
  ** (intArray.missing_i prefix_pre retval_2 (0 : Int) (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_16 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval_2)) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1))) (PreH4 : ((best + 1) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1) retval)) (PreH9 : ((0 : Int) <= retval)) (PreH10 : (retval < (n_pre + 1))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH14 : (lo <= (best - 1))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH17 : (NodeHeapState slots_out (hsize - 1))) (PreH18 : (FrontierPopTop pop_slots hsize slots_out)) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre) + 1) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps)) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests)) (PreH38 : ((0 : Int) <= t)) (PreH39 : (t < k_pre)) (PreH40 : ((0 : Int) < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t)) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH44 : (NodeHeapState pop_slots hsize)) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : ((0 : Int) <= (start - 1))) (PreH49 : ((start - 1) < (n_pre + 1))) (PreH50 : (((start + L_pre) - 1) <= lo)) (PreH51 : ((0 : Int) <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps (best + 1) hi retval_2) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval_2) ” &&
  “ (retval_2 <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (RangeArgmax query_ps lo (best - 1) retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ (lo <= retval) ” &&
  “ (retval <= (best - 1)) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1) * sizeof(INT)))) # Int |-> ((Znth (start - 1) query_ps (0 : Int))))
  ** (intArray.missing_i prefix_pre (start - 1) (0 : Int) (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_17 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps (best + 1) hi retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval) ” &&
  “ (retval <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((prefix_pre + (retval * sizeof(INT)))) # Int |-> ((Znth retval query_ps (0 : Int))))
  ** (intArray.missing_i prefix_pre retval (0 : Int) (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_18 : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (vals : (List Int)) (starts : (List Int)) (los : (List Int)) (his : (List Int)) (bests : (List Int)) (chosen : (List Int)) (value : Int) (start : Int) (lo : Int) (hi : Int) (best : Int) (heap_cap : Int) (t : Int) (hsize : Int) (total : Int) (pop_slots : (List ((((Int × Int) × Int) × Int) × Int))) (vals_out : (List Int)) (starts_out : (List Int)) (los_out : (List Int)) (his_out : (List Int)) (bests_out : (List Int)) (slots_out : (List ((((Int × Int) × Int) × Int) × Int))) (query_ps : (List Int)) (query_st_slots : (List Int)) (retval : Int) (PreH1 : (RangeArgmax query_ps (best + 1) hi retval)) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < (n_pre + 1))) (PreH4 : ((best + 1) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH7 : ((best + 1) <= hi)) (PreH8 : (lo > (best - 1))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out)) (PreH11 : (NodeHeapState slots_out (hsize - 1))) (PreH12 : (FrontierPopTop pop_slots hsize slots_out)) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre) + 1) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps)) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1))) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans)) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests)) (PreH32 : ((0 : Int) <= t)) (PreH33 : (t < k_pre)) (PreH34 : ((0 : Int) < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t)) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots)))) (PreH38 : (NodeHeapState pop_slots hsize)) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best)) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : ((0 : Int) <= (start - 1))) (PreH43 : ((start - 1) < (n_pre + 1))) (PreH44 : (((start + L_pre) - 1) <= lo)) (PreH45 : ((0 : Int) <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full prefix_pre (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (RangeArgmax query_ps (best + 1) hi retval) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < (n_pre + 1)) ” &&
  “ ((best + 1) <= retval) ” &&
  “ (retval <= hi) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (lo > (best - 1)) ” &&
  “ ((Zlength (slots_out)) = heap_cap) ” &&
  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out) ” &&
  “ (NodeHeapState slots_out (hsize - 1)) ” &&
  “ (FrontierPopTop pop_slots hsize slots_out) ” &&
  “ (value = (heap_top_value (pop_slots))) ” &&
  “ (start = (heap_top_start (pop_slots))) ” &&
  “ (lo = (heap_top_lo (pop_slots))) ” &&
  “ (hi = (heap_top_hi (pop_slots))) ” &&
  “ (best = (heap_top_best (pop_slots))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l query_ps) ” &&
  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (pop_slots)) = heap_cap) ” &&
  “ (NodeArrays pop_slots vals starts los his bests) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) < hsize) ” &&
  “ (hsize <= heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) ” &&
  “ (NodeHeapState pop_slots hsize) ” &&
  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ (((start + L_pre) - 1) <= lo) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1) * sizeof(INT)))) # Int |-> ((Znth (start - 1) query_ps (0 : Int))))
  ** (intArray.missing_i prefix_pre (start - 1) (0 : Int) (n_pre + 1) query_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) query_st_slots)
  ** (intArray.full heap_value_pre heap_cap vals_out)
  ** (intArray.full heap_start_pre heap_cap starts_out)
  ** (intArray.full heap_lo_pre heap_cap los_out)
  ** (intArray.full heap_hi_pre heap_cap his_out)
  ** (intArray.full heap_best_pre heap_cap bests_out)
  ** (intArray.full arr_pre n_pre l)

noncomputable def superPiano_partial_solve_wit_19_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : ((best + 1) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ”

noncomputable def superPiano_partial_solve_wit_19_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (left_best : Int) (lo : Int) (left_value : Int) (total : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : ((best + 1) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (RangeArgmax push_ps (best + 1) hi right_best)) (PreH40 : ((0 : Int) <= right_best)) (PreH41 : (right_best < (n_pre + 1))) (PreH42 : ((best + 1) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH46 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l push_ps) ” &&
  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int)))) (sublist ((0 : Int)) (hsize) (push_slots))) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best + 1) <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax push_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (RangeArgmax push_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_19 : Prop := superPiano_partial_solve_wit_19_pure -> superPiano_partial_solve_wit_19_aux

noncomputable def superPiano_partial_solve_wit_20_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = (0 : Int))) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (hi <= best)) (PreH40 : (right_best = (0 : Int))) (PreH41 : (right_value = (0 : Int))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ”

noncomputable def superPiano_partial_solve_wit_20_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (left_best : Int) (best : Int) (lo : Int) (start : Int) (left_value : Int) (total : Int) (hi : Int) (right_best : Int) (right_value : Int) (value : Int) (push_ps : (List Int)) (push_slots : (List ((((Int × Int) × Int) × Int) × Int))) (push_vals : (List Int)) (push_starts : (List Int)) (push_los : (List Int)) (push_his : (List Int)) (push_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps)) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = (0 : Int))) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots)))) (PreH23 : (NodeHeapState push_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= (best - 1))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1) left_best)) (PreH34 : ((0 : Int) <= left_best)) (PreH35 : (left_best < (n_pre + 1))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH39 : (hi <= best)) (PreH40 : (right_best = (0 : Int))) (PreH41 : (right_value = (0 : Int))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best)) (PreH43 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l push_ps) ” &&
  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (push_slots)) = heap_cap) ” &&
  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = (0 : Int)) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState push_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (left_value) (start) (lo) ((best - 1)) (left_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (push_slots))) ” &&
  “ (NodeHeapState push_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ (best <= hi) ” &&
  “ (hi <= n_pre) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax push_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (hi <= best) ” &&
  “ (right_best = (0 : Int)) ” &&
  “ (right_value = (0 : Int)) ” &&
  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap push_vals)
  ** (intArray.full heap_start_pre heap_cap push_starts)
  ** (intArray.full heap_lo_pre heap_cap push_los)
  ** (intArray.full heap_hi_pre heap_cap push_his)
  ** (intArray.full heap_best_pre heap_cap push_bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) push_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_20 : Prop := superPiano_partial_solve_wit_20_pure -> superPiano_partial_solve_wit_20_aux

noncomputable def superPiano_partial_solve_wit_21_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH23 : (NodeHeapState right_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1) <= hi)) (PreH31 : ((0 : Int) <= (best + 1))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH34 : ((0 : Int) <= right_best)) (PreH35 : (right_best < (n_pre + 1))) (PreH36 : ((best + 1) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= (best - 1))) (PreH41 : ((best - 1) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH43 : ((0 : Int) <= left_best)) (PreH44 : (left_best < (n_pre + 1))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (right_slots)) = heap_cap) ” &&
  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests) ” &&
  “ (NodeHeapState right_slots hsize) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ”

noncomputable def superPiano_partial_solve_wit_21_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (left_best : Int) (left_value : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : ((0 : Int) <= t)) (PreH18 : (t < k_pre)) (PreH19 : ((0 : Int) <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t)) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH23 : (NodeHeapState right_slots hsize)) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= (start - 1))) (PreH27 : ((start - 1) < (n_pre + 1))) (PreH28 : ((0 : Int) <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1) <= hi)) (PreH31 : ((0 : Int) <= (best + 1))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH34 : ((0 : Int) <= right_best)) (PreH35 : (right_best < (n_pre + 1))) (PreH36 : ((best + 1) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH39 : ((0 : Int) <= lo)) (PreH40 : (lo <= (best - 1))) (PreH41 : ((best - 1) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1) left_best)) (PreH43 : ((0 : Int) <= left_best)) (PreH44 : (left_best < (n_pre + 1))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best)) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (right_slots)) = heap_cap) ” &&
  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests) ” &&
  “ (NodeHeapState right_slots hsize) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l right_ps) ” &&
  “ (SparseArgmaxBuilt right_ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (right_slots)) = heap_cap) ” &&
  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests) ” &&
  “ (has_left = 1) ” &&
  “ (has_right = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((hsize + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots))) ” &&
  “ (NodeHeapState right_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ ((best + 1) <= hi) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ (hi <= n_pre) ” &&
  “ (RangeArgmax right_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= (best - 1)) ” &&
  “ ((best - 1) <= n_pre) ” &&
  “ (RangeArgmax right_ps lo (best - 1) left_best) ” &&
  “ ((0 : Int) <= left_best) ” &&
  “ (left_best < (n_pre + 1)) ” &&
  “ (lo <= left_best) ” &&
  “ (left_best <= (best - 1)) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_21 : Prop := superPiano_partial_solve_wit_21_pure -> superPiano_partial_solve_wit_21_aux

noncomputable def superPiano_partial_solve_wit_22_pure : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (left_best = (0 : Int))) (PreH17 : (left_value = (0 : Int))) (PreH18 : (has_right = 1)) (PreH19 : ((0 : Int) <= t)) (PreH20 : (t < k_pre)) (PreH21 : ((0 : Int) <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH25 : (NodeHeapState right_slots hsize)) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : ((0 : Int) <= (start - 1))) (PreH29 : ((start - 1) < (n_pre + 1))) (PreH30 : ((0 : Int) <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1) <= hi)) (PreH33 : ((0 : Int) <= (best + 1))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH36 : ((0 : Int) <= right_best)) (PreH37 : (right_best < (n_pre + 1))) (PreH38 : ((best + 1) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "L" ) )) # Int |-> (L_pre))
  ** ((( &( "R" ) )) # Int |-> (R_pre))
  ** ((( &( "prefix" ) )) # Ptr |-> (prefix_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "heap_value" ) )) # Ptr |-> (heap_value_pre))
  ** ((( &( "heap_start" ) )) # Ptr |-> (heap_start_pre))
  ** ((( &( "heap_lo" ) )) # Ptr |-> (heap_lo_pre))
  ** ((( &( "heap_hi" ) )) # Ptr |-> (heap_hi_pre))
  ** ((( &( "heap_best" ) )) # Ptr |-> (heap_best_pre))
  ** ((( &( "heap_cap" ) )) # Int |-> (heap_cap))
  ** ((( &( "has_left" ) )) # Int |-> (has_left))
  ** ((( &( "left_best" ) )) # Int |-> (left_best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** ((( &( "has_right" ) )) # Int |-> (has_right))
  ** ((( &( "t" ) )) # Int |-> (t))
  ** ((( &( "hsize" ) )) # Int |-> (hsize))
  ** ((( &( "right_best" ) )) # Int |-> (right_best))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "right_value" ) )) # Int |-> (right_value))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (right_slots)) = heap_cap) ” &&
  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests) ” &&
  “ (NodeHeapState right_slots hsize) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ”

noncomputable def superPiano_partial_solve_wit_22_aux : Prop :=
  forall (heap_best_pre : Int) (heap_hi_pre : Int) (heap_lo_pre : Int) (heap_start_pre : Int) (heap_value_pre : Int) (st_pre : Int) (prefix_pre : Int) (R_pre : Int) (L_pre : Int) (k_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (st_slots : (List Int)) (chosen : (List Int)) (heap_cap : Int) (has_left : Int) (left_best : Int) (left_value : Int) (has_right : Int) (t : Int) (hsize : Int) (right_best : Int) (hi : Int) (best : Int) (start : Int) (right_value : Int) (total : Int) (lo : Int) (value : Int) (right_ps : (List Int)) (right_slots : (List ((((Int × Int) × Int) × Int) × Int))) (right_vals : (List Int)) (right_starts : (List Int)) (right_los : (List Int)) (right_his : (List Int)) (right_bests : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre) + 1) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre) + 1))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps)) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1))) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans)) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests)) (PreH15 : (has_left = (0 : Int))) (PreH16 : (left_best = (0 : Int))) (PreH17 : (left_value = (0 : Int))) (PreH18 : (has_right = 1)) (PreH19 : ((0 : Int) <= t)) (PreH20 : (t < k_pre)) (PreH21 : ((0 : Int) <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1) + (k_pre - t)) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots)))) (PreH25 : (NodeHeapState right_slots hsize)) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : ((0 : Int) <= (start - 1))) (PreH29 : ((start - 1) < (n_pre + 1))) (PreH30 : ((0 : Int) <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1) <= hi)) (PreH33 : ((0 : Int) <= (best + 1))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1) hi right_best)) (PreH36 : ((0 : Int) <= right_best)) (PreH37 : (right_best < (n_pre + 1))) (PreH38 : ((best + 1) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best)) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best)) (PreH42 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000)))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)
  ** (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
|--
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ ((Zlength (right_slots)) = heap_cap) ” &&
  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests) ” &&
  “ (NodeHeapState right_slots hsize) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= L_pre) ” &&
  “ (L_pre <= R_pre) ” &&
  “ (R_pre <= n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (((n_pre + k_pre) + 1) <= 200000) ” &&
  “ (heap_cap = ((n_pre + k_pre) + 1)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (PrefixSums l right_ps) ” &&
  “ (SparseArgmaxBuilt right_ps st_slots (n_pre + 1)) ” &&
  “ (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans) ” &&
  “ ((Zlength (right_slots)) = heap_cap) ” &&
  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests) ” &&
  “ (has_left = (0 : Int)) ” &&
  “ (left_best = (0 : Int)) ” &&
  “ (left_value = (0 : Int)) ” &&
  “ (has_right = 1) ” &&
  “ ((0 : Int) <= t) ” &&
  “ (t < k_pre) ” &&
  “ ((0 : Int) <= hsize) ” &&
  “ (hsize < heap_cap) ” &&
  “ (((hsize + 1) + (k_pre - t)) < heap_cap) ” &&
  “ (FrontierSplitState right_ps n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen) (t + 1) total ((mkNode (right_value) (start) ((best + 1)) (hi) (right_best)) :: (@List.nil ((((Int × Int) × Int) × Int) × Int))) (sublist ((0 : Int)) (hsize) (right_slots))) ” &&
  “ (NodeHeapState right_slots hsize) ” &&
  “ (1 <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (start - 1)) ” &&
  “ ((start - 1) < (n_pre + 1)) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= best) ” &&
  “ ((best + 1) <= hi) ” &&
  “ ((0 : Int) <= (best + 1)) ” &&
  “ (hi <= n_pre) ” &&
  “ (RangeArgmax right_ps (best + 1) hi right_best) ” &&
  “ ((0 : Int) <= right_best) ” &&
  “ (right_best < (n_pre + 1)) ” &&
  “ ((best + 1) <= right_best) ” &&
  “ (right_best <= hi) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1) hi right_best) ” &&
  “ (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) ”
  &&  (intArray.full heap_value_pre heap_cap right_vals)
  ** (intArray.full heap_start_pre heap_cap right_starts)
  ** (intArray.full heap_lo_pre heap_cap right_los)
  ** (intArray.full heap_hi_pre heap_cap right_his)
  ** (intArray.full heap_best_pre heap_cap right_bests)
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full prefix_pre (n_pre + 1) right_ps)
  ** (intArray.full st_pre ((n_pre + 1) * ST_LEVELS) st_slots)

noncomputable def superPiano_partial_solve_wit_22 : Prop := superPiano_partial_solve_wit_22_pure -> superPiano_partial_solve_wit_22_aux


structure VC_Correct : Type where
  proof_of_build_prefix_safety_wit_1 : build_prefix_safety_wit_1
  proof_of_build_prefix_safety_wit_2 : build_prefix_safety_wit_2
  proof_of_build_prefix_safety_wit_3 : build_prefix_safety_wit_3
  proof_of_build_prefix_safety_wit_4 : build_prefix_safety_wit_4
  proof_of_build_prefix_safety_wit_5 : build_prefix_safety_wit_5
  proof_of_build_prefix_safety_wit_7 : build_prefix_safety_wit_7
  proof_of_build_prefix_partial_solve_wit_1 : build_prefix_partial_solve_wit_1
  proof_of_build_prefix_partial_solve_wit_2 : build_prefix_partial_solve_wit_2
  proof_of_build_prefix_partial_solve_wit_3 : build_prefix_partial_solve_wit_3
  proof_of_build_prefix_partial_solve_wit_4 : build_prefix_partial_solve_wit_4
  proof_of_superPiano_safety_wit_1 : superPiano_safety_wit_1
  proof_of_superPiano_safety_wit_2 : superPiano_safety_wit_2
  proof_of_superPiano_safety_wit_3 : superPiano_safety_wit_3
  proof_of_superPiano_safety_wit_4 : superPiano_safety_wit_4
  proof_of_superPiano_safety_wit_5 : superPiano_safety_wit_5
  proof_of_superPiano_safety_wit_6 : superPiano_safety_wit_6
  proof_of_superPiano_safety_wit_7 : superPiano_safety_wit_7
  proof_of_superPiano_safety_wit_8 : superPiano_safety_wit_8
  proof_of_superPiano_safety_wit_9 : superPiano_safety_wit_9
  proof_of_superPiano_safety_wit_11 : superPiano_safety_wit_11
  proof_of_superPiano_safety_wit_12 : superPiano_safety_wit_12
  proof_of_superPiano_safety_wit_13 : superPiano_safety_wit_13
  proof_of_superPiano_safety_wit_14 : superPiano_safety_wit_14
  proof_of_superPiano_safety_wit_15 : superPiano_safety_wit_15
  proof_of_superPiano_safety_wit_16 : superPiano_safety_wit_16
  proof_of_superPiano_safety_wit_17 : superPiano_safety_wit_17
  proof_of_superPiano_safety_wit_18 : superPiano_safety_wit_18
  proof_of_superPiano_safety_wit_19 : superPiano_safety_wit_19
  proof_of_superPiano_safety_wit_20 : superPiano_safety_wit_20
  proof_of_superPiano_safety_wit_21 : superPiano_safety_wit_21
  proof_of_superPiano_safety_wit_22 : superPiano_safety_wit_22
  proof_of_superPiano_safety_wit_24 : superPiano_safety_wit_24
  proof_of_superPiano_safety_wit_25 : superPiano_safety_wit_25
  proof_of_superPiano_safety_wit_26 : superPiano_safety_wit_26
  proof_of_superPiano_safety_wit_27 : superPiano_safety_wit_27
  proof_of_superPiano_safety_wit_28 : superPiano_safety_wit_28
  proof_of_superPiano_safety_wit_29 : superPiano_safety_wit_29
  proof_of_superPiano_safety_wit_30 : superPiano_safety_wit_30
  proof_of_superPiano_safety_wit_31 : superPiano_safety_wit_31
  proof_of_superPiano_safety_wit_32 : superPiano_safety_wit_32
  proof_of_superPiano_safety_wit_33 : superPiano_safety_wit_33
  proof_of_superPiano_safety_wit_34 : superPiano_safety_wit_34
  proof_of_superPiano_safety_wit_35 : superPiano_safety_wit_35
  proof_of_superPiano_safety_wit_36 : superPiano_safety_wit_36
  proof_of_superPiano_safety_wit_37 : superPiano_safety_wit_37
  proof_of_superPiano_safety_wit_38 : superPiano_safety_wit_38
  proof_of_superPiano_safety_wit_40 : superPiano_safety_wit_40
  proof_of_superPiano_safety_wit_41 : superPiano_safety_wit_41
  proof_of_superPiano_safety_wit_43 : superPiano_safety_wit_43
  proof_of_superPiano_safety_wit_44 : superPiano_safety_wit_44
  proof_of_superPiano_safety_wit_45 : superPiano_safety_wit_45
  proof_of_superPiano_safety_wit_46 : superPiano_safety_wit_46
  proof_of_superPiano_safety_wit_47 : superPiano_safety_wit_47
  proof_of_superPiano_safety_wit_48 : superPiano_safety_wit_48
  proof_of_superPiano_safety_wit_49 : superPiano_safety_wit_49
  proof_of_superPiano_safety_wit_50 : superPiano_safety_wit_50
  proof_of_superPiano_safety_wit_51 : superPiano_safety_wit_51
  proof_of_superPiano_safety_wit_52 : superPiano_safety_wit_52
  proof_of_superPiano_safety_wit_53 : superPiano_safety_wit_53
  proof_of_superPiano_safety_wit_54 : superPiano_safety_wit_54
  proof_of_superPiano_safety_wit_55 : superPiano_safety_wit_55
  proof_of_superPiano_safety_wit_56 : superPiano_safety_wit_56
  proof_of_superPiano_safety_wit_57 : superPiano_safety_wit_57
  proof_of_superPiano_safety_wit_58 : superPiano_safety_wit_58
  proof_of_superPiano_safety_wit_59 : superPiano_safety_wit_59
  proof_of_superPiano_safety_wit_60 : superPiano_safety_wit_60
  proof_of_superPiano_safety_wit_61 : superPiano_safety_wit_61
  proof_of_superPiano_safety_wit_62 : superPiano_safety_wit_62
  proof_of_superPiano_safety_wit_63 : superPiano_safety_wit_63
  proof_of_superPiano_safety_wit_64 : superPiano_safety_wit_64
  proof_of_superPiano_safety_wit_65 : superPiano_safety_wit_65
  proof_of_superPiano_safety_wit_66 : superPiano_safety_wit_66
  proof_of_superPiano_safety_wit_67 : superPiano_safety_wit_67
  proof_of_superPiano_safety_wit_68 : superPiano_safety_wit_68
  proof_of_superPiano_safety_wit_69 : superPiano_safety_wit_69
  proof_of_superPiano_entail_wit_2 : superPiano_entail_wit_2
  proof_of_superPiano_entail_wit_10_1 : superPiano_entail_wit_10_1
  proof_of_superPiano_entail_wit_10_2 : superPiano_entail_wit_10_2
  proof_of_superPiano_entail_wit_10_3 : superPiano_entail_wit_10_3
  proof_of_superPiano_entail_wit_11_1 : superPiano_entail_wit_11_1
  proof_of_superPiano_entail_wit_11_2 : superPiano_entail_wit_11_2
  proof_of_superPiano_entail_wit_11_3 : superPiano_entail_wit_11_3
  proof_of_superPiano_entail_wit_11_4 : superPiano_entail_wit_11_4
  proof_of_superPiano_entail_wit_12_1 : superPiano_entail_wit_12_1
  proof_of_superPiano_entail_wit_12_2 : superPiano_entail_wit_12_2
  proof_of_superPiano_partial_solve_wit_1 : superPiano_partial_solve_wit_1
  proof_of_superPiano_partial_solve_wit_2 : superPiano_partial_solve_wit_2
  proof_of_superPiano_partial_solve_wit_3 : superPiano_partial_solve_wit_3
  proof_of_superPiano_partial_solve_wit_4_pure : superPiano_partial_solve_wit_4_pure
  proof_of_superPiano_partial_solve_wit_4 : superPiano_partial_solve_wit_4
  proof_of_superPiano_partial_solve_wit_5_pure : superPiano_partial_solve_wit_5_pure
  proof_of_superPiano_partial_solve_wit_5 : superPiano_partial_solve_wit_5
  proof_of_superPiano_partial_solve_wit_6_pure : superPiano_partial_solve_wit_6_pure
  proof_of_superPiano_partial_solve_wit_6 : superPiano_partial_solve_wit_6
  proof_of_superPiano_partial_solve_wit_7_pure : superPiano_partial_solve_wit_7_pure
  proof_of_superPiano_partial_solve_wit_7 : superPiano_partial_solve_wit_7
  proof_of_superPiano_partial_solve_wit_8_pure : superPiano_partial_solve_wit_8_pure
  proof_of_superPiano_partial_solve_wit_8 : superPiano_partial_solve_wit_8
  proof_of_superPiano_partial_solve_wit_9_pure : superPiano_partial_solve_wit_9_pure
  proof_of_superPiano_partial_solve_wit_9 : superPiano_partial_solve_wit_9
  proof_of_superPiano_partial_solve_wit_10_pure : superPiano_partial_solve_wit_10_pure
  proof_of_superPiano_partial_solve_wit_10 : superPiano_partial_solve_wit_10
  proof_of_superPiano_partial_solve_wit_11 : superPiano_partial_solve_wit_11
  proof_of_superPiano_partial_solve_wit_12 : superPiano_partial_solve_wit_12
  proof_of_superPiano_partial_solve_wit_13_pure : superPiano_partial_solve_wit_13_pure
  proof_of_superPiano_partial_solve_wit_13 : superPiano_partial_solve_wit_13
  proof_of_superPiano_partial_solve_wit_14_pure : superPiano_partial_solve_wit_14_pure
  proof_of_superPiano_partial_solve_wit_14 : superPiano_partial_solve_wit_14
  proof_of_superPiano_partial_solve_wit_15 : superPiano_partial_solve_wit_15
  proof_of_superPiano_partial_solve_wit_16 : superPiano_partial_solve_wit_16
  proof_of_superPiano_partial_solve_wit_17 : superPiano_partial_solve_wit_17
  proof_of_superPiano_partial_solve_wit_18 : superPiano_partial_solve_wit_18
  proof_of_superPiano_partial_solve_wit_19_pure : superPiano_partial_solve_wit_19_pure
  proof_of_superPiano_partial_solve_wit_19 : superPiano_partial_solve_wit_19
  proof_of_superPiano_partial_solve_wit_20_pure : superPiano_partial_solve_wit_20_pure
  proof_of_superPiano_partial_solve_wit_20 : superPiano_partial_solve_wit_20
  proof_of_superPiano_partial_solve_wit_21_pure : superPiano_partial_solve_wit_21_pure
  proof_of_superPiano_partial_solve_wit_21 : superPiano_partial_solve_wit_21
  proof_of_superPiano_partial_solve_wit_22_pure : superPiano_partial_solve_wit_22_pure
  proof_of_superPiano_partial_solve_wit_22 : superPiano_partial_solve_wit_22
  proof_of_build_prefix_safety_wit_6 : build_prefix_safety_wit_6
  proof_of_build_prefix_entail_wit_1 : build_prefix_entail_wit_1
  proof_of_build_prefix_entail_wit_2 : build_prefix_entail_wit_2
  proof_of_build_prefix_entail_wit_3 : build_prefix_entail_wit_3
  proof_of_build_prefix_return_wit_1 : build_prefix_return_wit_1
  proof_of_superPiano_safety_wit_10 : superPiano_safety_wit_10
  proof_of_superPiano_safety_wit_23 : superPiano_safety_wit_23
  proof_of_superPiano_safety_wit_39 : superPiano_safety_wit_39
  proof_of_superPiano_safety_wit_42 : superPiano_safety_wit_42
  proof_of_superPiano_entail_wit_1 : superPiano_entail_wit_1
  proof_of_superPiano_entail_wit_3 : superPiano_entail_wit_3
  proof_of_superPiano_entail_wit_4 : superPiano_entail_wit_4
  proof_of_superPiano_entail_wit_5 : superPiano_entail_wit_5
  proof_of_superPiano_entail_wit_6 : superPiano_entail_wit_6
  proof_of_superPiano_entail_wit_7 : superPiano_entail_wit_7
  proof_of_superPiano_entail_wit_8 : superPiano_entail_wit_8
  proof_of_superPiano_entail_wit_9 : superPiano_entail_wit_9
  proof_of_superPiano_entail_wit_13 : superPiano_entail_wit_13
  proof_of_superPiano_entail_wit_14 : superPiano_entail_wit_14
  proof_of_superPiano_entail_wit_15_1 : superPiano_entail_wit_15_1
  proof_of_superPiano_entail_wit_15_2 : superPiano_entail_wit_15_2
  proof_of_superPiano_entail_wit_15_3 : superPiano_entail_wit_15_3
  proof_of_superPiano_entail_wit_15_4 : superPiano_entail_wit_15_4
  proof_of_superPiano_entail_wit_16 : superPiano_entail_wit_16
  proof_of_superPiano_return_wit_1 : superPiano_return_wit_1
  proof_of_superPiano_partial_solve_wit_1_pure : superPiano_partial_solve_wit_1_pure
  proof_of_superPiano_partial_solve_wit_2_pure : superPiano_partial_solve_wit_2_pure
  proof_of_superPiano_partial_solve_wit_3_pure : superPiano_partial_solve_wit_3_pure

end SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_goal
