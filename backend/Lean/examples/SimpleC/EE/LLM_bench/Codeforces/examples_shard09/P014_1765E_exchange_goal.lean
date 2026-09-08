import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance P014_1765E_exchange_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ ((((n_pre + a_pre) - 1) ≠ (-9223372036854775808)) ∨ (a_pre ≠ (-1))) ” &&
  “ (a_pre ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ (((n_pre + a_pre) - 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((n_pre + a_pre) - 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ ((n_pre + a_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (n_pre + a_pre)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre (Z.quot ((n_pre + a_pre) - 1) a_pre)) ”
  &&  emp
) \/
(
forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre (Z.quot ((n_pre + a_pre) - 1) a_pre)) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  (Spec n_pre a_pre b_pre (Z.quot ((n_pre + a_pre) - 1) a_pre))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre 1) ”
  &&  emp
) \/
(
forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre 1) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (n_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  (Spec n_pre a_pre b_pre 1)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_goal
