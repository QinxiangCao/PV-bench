import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance P012_1326A_bad_ugly_numbers_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def solver_safety_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.undef_full out_pre 100001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.undef_full out_pre 100001)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.undef_full out_pre 100001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.undef_full out_pre 100001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.undef_full out_pre 100001)
|--
  “ (50 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 50) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (((out_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (50))
  ** (charArray.undef_seg out_pre 1 100001)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (chars : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth (0 : Int) chars (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars (0 : Int)) = 51))) ,
  (charArray.seg out_pre (0 : Int) (i + 1) (chars ++ ((51 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (i + 1) 100001)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (chars : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth (0 : Int) chars (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars (0 : Int)) = 51))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.seg out_pre (0 : Int) i chars)
  ** (charArray.undef_seg out_pre i 100001)
|--
  “ (51 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 51) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (chars : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth (0 : Int) chars (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars (0 : Int)) = 51))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.seg out_pre (0 : Int) i chars)
  ** (charArray.undef_seg out_pre i 100001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (((out_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (50))
  ** (charArray.undef_seg out_pre 1 100001)
|--
  EX chars : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (chars)) = 1) ” &&
  “ ((Znth (0 : Int) chars (0 : Int)) = 50) ” &&
  “ forall (k : Int) , (((1 <= k) ∧ (k < 1)) -> ((Znth k chars (0 : Int)) = 51)) ”
  &&  (charArray.seg out_pre (0 : Int) 1 chars)
  ** (charArray.undef_seg out_pre 1 100001)
) \/
(
forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (((out_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (50))
|--
  EX chars : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (chars)) = 1) ” &&
  “ ((Znth (0 : Int) chars (0 : Int)) = 50) ” &&
  “ forall (k : Int) , (((1 <= k) ∧ (k < 1)) -> ((Znth k chars (0 : Int)) = 51)) ”
  &&  (charArray.seg out_pre (0 : Int) 1 chars)
)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (chars_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth (0 : Int) chars_2 (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars_2 (0 : Int)) = 51))) ,
  (charArray.seg out_pre (0 : Int) (i + 1) (chars_2 ++ ((51 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (i + 1) 100001)
|--
  EX chars : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (chars)) = (i + 1)) ” &&
  “ ((Znth (0 : Int) chars (0 : Int)) = 50) ” &&
  “ forall (k : Int) , (((1 <= k) ∧ (k < (i + 1))) -> ((Znth k chars (0 : Int)) = 51)) ”
  &&  (charArray.seg out_pre (0 : Int) (i + 1) chars)
  ** (charArray.undef_seg out_pre (i + 1) 100001)
) \/
(
forall (n_pre : Int) (chars_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth (0 : Int) chars_2 (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars_2 (0 : Int)) = 51))) ,
  TT && emp 
|--
  “ ((Znth (0 : Int) (chars_2 ++ (51 :: (@List.nil Int))) (0 : Int)) = 50) ” &&
  “ ((Zlength ((chars_2 ++ (51 :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (chars_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth (0 : Int) chars_2 (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars_2 (0 : Int)) = 51))) ,
  ((Znth (0 : Int) (chars_2 ++ (51 :: (@List.nil Int))) (0 : Int)) = 50)

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (chars_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i)) (PreH7 : ((Znth (0 : Int) chars_2 (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars_2 (0 : Int)) = 51))) ,
  ((Zlength ((chars_2 ++ (51 :: (@List.nil Int))))) = (i + 1))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (chars_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i_2)) (PreH7 : ((Znth (0 : Int) chars_2 (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i_2)) -> ((Znth k chars_2 (0 : Int)) = 51))) ,
  (charArray.seg out_pre (0 : Int) (i_2 + 1) (chars_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (i_2 + 1) 100001)
|--
  EX chars : (List Int), EX digits : (List Int),
  “ (Spec n_pre (Some (digits))) ” &&
  “ ((Zlength (chars)) = (Zlength (digits))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (digits)))) -> ((Znth i chars (0 : Int)) = ((Znth i digits (0 : Int)) + 48))) ” &&
  “ (n_pre = (Zlength (digits))) ”
  &&  (charArray.full out_pre ((Zlength (chars)) + 1) (chars ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre ((Zlength (chars)) + 1) 100001)
) \/
(
forall (out_pre : Int) (n_pre : Int) (chars_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : ((Zlength (chars_2)) = i_2)) (PreH7 : ((Znth (0 : Int) chars_2 (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i_2)) -> ((Znth k chars_2 (0 : Int)) = 51))) ,
  (charArray.seg out_pre (0 : Int) (i_2 + 1) (chars_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (i_2 + 1) 100001)
|--
  EX chars : (List Int), EX digits : (List Int),
  “ (Spec n_pre (Some (digits))) ” &&
  “ ((Zlength (chars)) = (Zlength (digits))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (digits)))) -> ((Znth i chars (0 : Int)) = ((Znth i digits (0 : Int)) + 48))) ” &&
  “ (n_pre = (Zlength (digits))) ”
  &&  (charArray.full out_pre ((Zlength (chars)) + 1) (chars ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre ((Zlength (chars)) + 1) 100001)
)

noncomputable def solver_return_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (charArray.undef_full out_pre 100001)
|--
  (“ ((-1) = (-1)) ” &&
  “ (Spec n_pre None) ”
  &&  (charArray.undef_full out_pre 100001))
  ||
  (EX chars : (List Int), EX digits : (List Int),
  “ (Spec n_pre (Some (digits))) ” &&
  “ ((Zlength (chars)) = (Zlength (digits))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (digits)))) -> ((Znth i chars (0 : Int)) = ((Znth i digits (0 : Int)) + 48))) ” &&
  “ ((-1) = (Zlength (digits))) ”
  &&  (charArray.full out_pre ((Zlength (chars)) + 1) (chars ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre ((Zlength (chars)) + 1) 100001))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (charArray.undef_full out_pre 100001)
|--
  “ (n_pre ≠ 1) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ”
  &&  (((out_pre + ((0 : Int) * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg out_pre 1 100001)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (chars : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth (0 : Int) chars (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars (0 : Int)) = 51))) ,
  (charArray.seg out_pre (0 : Int) i chars)
  ** (charArray.undef_seg out_pre i 100001)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (chars)) = i) ” &&
  “ ((Znth (0 : Int) chars (0 : Int)) = 50) ” &&
  “ forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars (0 : Int)) = 51)) ”
  &&  (((out_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg out_pre (i + 1) 100001)
  ** (charArray.seg out_pre (0 : Int) i chars)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (chars : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (chars)) = i)) (PreH7 : ((Znth (0 : Int) chars (0 : Int)) = 50)) (PreH8 : forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars (0 : Int)) = 51))) ,
  (charArray.seg out_pre (0 : Int) i chars)
  ** (charArray.undef_seg out_pre i 100001)
|--
  “ (i >= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (chars)) = i) ” &&
  “ ((Znth (0 : Int) chars (0 : Int)) = 50) ” &&
  “ forall (k : Int) , (((1 <= k) ∧ (k < i)) -> ((Znth k chars (0 : Int)) = 51)) ”
  &&  (((out_pre + (n_pre * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_missing_i out_pre n_pre i 100001)
  ** (charArray.seg out_pre (0 : Int) i chars)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_goal
