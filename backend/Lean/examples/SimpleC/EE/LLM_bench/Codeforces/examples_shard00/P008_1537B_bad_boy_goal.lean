import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance P008_1537B_bad_boy_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "m" ) )) # Int64 |-> (m_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i_pre))
  ** ((( &( "j" ) )) # Int64 |-> (j_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 4)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "m" ) )) # Int64 |-> (m_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i_pre))
  ** ((( &( "j" ) )) # Int64 |-> (j_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 4)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
  ** (int64Array.undef_seg out_pre 1 4)
  ** ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "m" ) )) # Int64 |-> (m_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i_pre))
  ** ((( &( "j" ) )) # Int64 |-> (j_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
  ** (int64Array.undef_seg out_pre 1 4)
  ** ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "m" ) )) # Int64 |-> (m_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i_pre))
  ** ((( &( "j" ) )) # Int64 |-> (j_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (int64Array.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
  ** ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "m" ) )) # Int64 |-> (m_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i_pre))
  ** ((( &( "j" ) )) # Int64 |-> (j_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (int64Array.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT64)))) # Int64 |-> (n_pre))
  ** (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
  ** ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "m" ) )) # Int64 |-> (m_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i_pre))
  ** ((( &( "j" ) )) # Int64 |-> (j_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (int64Array.undef_seg out_pre (((1 + 1) + 1) + 1) 4)
  ** (((out_pre + (3 * sizeof(INT64)))) # Int64 |-> (m_pre))
  ** (((out_pre + (2 * sizeof(INT64)))) # Int64 |-> (n_pre))
  ** (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
|--
  EX p : (Int × Int), EX q : (Int × Int),
  “ (Spec n_pre m_pre start p q) ”
  &&  (int64Array.full out_pre 4 ((zpair_fst (p)) :: ((zpair_snd (p)) :: ((zpair_fst (q)) :: ((zpair_snd (q)) :: (@List.nil Int))))))
) \/
(
forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= 9223372036854775807)) (PreH2 : (n_pre <= 9223372036854775807)) (PreH3 : (m_pre <= 9223372036854775807)) (PreH4 : (1 >= (-9223372036854775808))) (PreH5 : (n_pre >= (-9223372036854775808))) (PreH6 : (m_pre >= (-9223372036854775808))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000000)) (PreH11 : (i_pre = (zpair_fst (start)))) (PreH12 : (j_pre = (zpair_snd (start)))) (PreH13 : (1 <= i_pre)) (PreH14 : (i_pre <= n_pre)) (PreH15 : (1 <= j_pre)) (PreH16 : (j_pre <= m_pre)) ,
  (((out_pre + (3 * sizeof(INT64)))) # Int64 |-> (m_pre))
  ** (((out_pre + (2 * sizeof(INT64)))) # Int64 |-> (n_pre))
  ** (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
|--
  EX p : (Int × Int), EX q : (Int × Int),
  “ (Spec n_pre m_pre start p q) ”
  &&  (int64Array.full out_pre 4 ((zpair_fst (p)) :: ((zpair_snd (p)) :: ((zpair_fst (q)) :: ((zpair_snd (q)) :: (@List.nil Int))))))
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (int64Array.undef_full out_pre 4)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000000) ” &&
  “ (i_pre = (zpair_fst (start))) ” &&
  “ (j_pre = (zpair_snd (start))) ” &&
  “ (1 <= i_pre) ” &&
  “ (i_pre <= n_pre) ” &&
  “ (1 <= j_pre) ” &&
  “ (j_pre <= m_pre) ”
  &&  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_seg out_pre 1 4)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
  ** (int64Array.undef_seg out_pre 1 4)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000000) ” &&
  “ (i_pre = (zpair_fst (start))) ” &&
  “ (j_pre = (zpair_snd (start))) ” &&
  “ (1 <= i_pre) ” &&
  “ (i_pre <= n_pre) ” &&
  “ (1 <= j_pre) ” &&
  “ (j_pre <= m_pre) ”
  &&  (((out_pre + (1 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (int64Array.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000000) ” &&
  “ (i_pre = (zpair_fst (start))) ” &&
  “ (j_pre = (zpair_snd (start))) ” &&
  “ (1 <= i_pre) ” &&
  “ (i_pre <= n_pre) ” &&
  “ (1 <= j_pre) ” &&
  “ (j_pre <= m_pre) ”
  &&  (((out_pre + (2 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_missing_i out_pre 2 (1 + 1) 4)
  ** (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (out_pre : Int) (j_pre : Int) (i_pre : Int) (m_pre : Int) (n_pre : Int) (start : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (i_pre = (zpair_fst (start)))) (PreH6 : (j_pre = (zpair_snd (start)))) (PreH7 : (1 <= i_pre)) (PreH8 : (i_pre <= n_pre)) (PreH9 : (1 <= j_pre)) (PreH10 : (j_pre <= m_pre)) ,
  (int64Array.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT64)))) # Int64 |-> (n_pre))
  ** (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000000) ” &&
  “ (i_pre = (zpair_fst (start))) ” &&
  “ (j_pre = (zpair_snd (start))) ” &&
  “ (1 <= i_pre) ” &&
  “ (i_pre <= n_pre) ” &&
  “ (1 <= j_pre) ” &&
  “ (j_pre <= m_pre) ”
  &&  (((out_pre + (3 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_missing_i out_pre 3 ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT64)))) # Int64 |-> (n_pre))
  ** (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> (1))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (1))


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_goal
