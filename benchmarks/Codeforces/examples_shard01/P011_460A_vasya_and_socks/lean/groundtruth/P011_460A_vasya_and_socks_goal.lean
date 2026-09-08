import SimpleC.SL.SeparationLogic

import Codeforces.examples_shard01.P011_460A_vasya_and_socks.lean.spec_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard01.P011_460A_vasya_and_socks.lean.groundtruth.P011_460A_vasya_and_socks_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance P011_460A_vasya_and_socks_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  ((( &( "days" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : ((0 : Int) <= days)) (PreH6 : (days <= 200)) (PreH7 : ((0 : Int) <= n)) (PreH8 : (n <= 100)) (PreH9 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH10 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "days" ) )) # Int |-> (days))
  ** ((( &( "n" ) )) # Int |-> (n))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (n > (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : ((0 : Int) <= days)) (PreH7 : (days <= 200)) (PreH8 : ((0 : Int) <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH11 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "days" ) )) # Int |-> (days))
  ** ((( &( "n" ) )) # Int |-> (n))
|--
  “ ((days + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (days + 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (n > (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : ((0 : Int) <= days)) (PreH7 : (days <= 200)) (PreH8 : ((0 : Int) <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH11 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "days" ) )) # Int |-> ((days + 1)))
  ** ((( &( "n" ) )) # Int |-> (n))
|--
  “ ((n - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n - 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (n > (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : ((0 : Int) <= days)) (PreH7 : (days <= 200)) (PreH8 : ((0 : Int) <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH11 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "days" ) )) # Int |-> ((days + 1)))
  ** ((( &( "n" ) )) # Int |-> ((n - 1)))
|--
  “ (((days + 1) ≠ (INT_MIN)) ∨ (m_pre ≠ (-1))) ” &&
  “ (m_pre ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (n > (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : ((0 : Int) <= days)) (PreH7 : (days <= 200)) (PreH8 : ((0 : Int) <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH11 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "days" ) )) # Int |-> ((days + 1)))
  ** ((( &( "n" ) )) # Int |-> ((n - 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) = (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "days" ) )) # Int |-> ((days + 1)))
  ** ((( &( "n" ) )) # Int |-> ((n - 1)))
|--
  “ (((n - 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n - 1) + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 200) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (n_pre = ((n_pre + (Z.quot (0 : Int) m_pre)) - (0 : Int))) ” &&
  “ forall (d : Int) , (((1 <= d) ∧ (d <= (0 : Int))) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int))) ”
  &&  emp
) \/
(
forall (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  TT && emp 
|--
  “ forall (d : Int) , (((1 <= d) ∧ (d <= (0 : Int))) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int))) ” &&
  “ (n_pre = ((n_pre + (Z.quot (0 : Int) m_pre)) - (0 : Int))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  forall (d : Int) , (((1 <= d) ∧ (d <= (0 : Int))) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  (n_pre = ((n_pre + (Z.quot (0 : Int) m_pre)) - (0 : Int)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) = (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ ((0 : Int) <= (days + 1)) ” &&
  “ ((days + 1) <= 200) ” &&
  “ ((0 : Int) <= ((n - 1) + 1)) ” &&
  “ (((n - 1) + 1) <= 100) ” &&
  “ (((n - 1) + 1) = ((n_pre + (Z.quot (days + 1) m_pre)) - (days + 1))) ” &&
  “ forall (d : Int) , (((1 <= d) ∧ (d <= (days + 1))) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int))) ”
  &&  emp
) \/
(
forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) = (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  TT && emp 
|--
  “ (((((n_pre + (Z.quot days m_pre)) - days) - 1) + 1) = ((n_pre + (Z.quot (days + 1) m_pre)) - (days + 1))) ” &&
  “ ((days + 1) <= 200) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) = (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  (((((n_pre + (Z.quot days m_pre)) - days) - 1) + 1) = ((n_pre + (Z.quot (days + 1) m_pre)) - (days + 1)))

noncomputable def solver_entail_wit_2_1_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) = (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((days + 1) <= 200)

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) ≠ (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ ((0 : Int) <= (days + 1)) ” &&
  “ ((days + 1) <= 200) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) <= 100) ” &&
  “ ((n - 1) = ((n_pre + (Z.quot (days + 1) m_pre)) - (days + 1))) ” &&
  “ forall (d : Int) , (((1 <= d) ∧ (d <= (days + 1))) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int))) ”
  &&  emp
) \/
(
forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) ≠ (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  TT && emp 
|--
  “ ((((n_pre + (Z.quot days m_pre)) - days) - 1) = ((n_pre + (Z.quot (days + 1) m_pre)) - (days + 1))) ” &&
  “ ((days + 1) <= 200) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) ≠ (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((((n_pre + (Z.quot days m_pre)) - days) - 1) = ((n_pre + (Z.quot (days + 1) m_pre)) - (days + 1)))

noncomputable def solver_entail_wit_2_2_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : ((Z.rem (days + 1) m_pre) ≠ (0 : Int))) (PreH2 : (n > (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : ((0 : Int) <= days)) (PreH8 : (days <= 200)) (PreH9 : ((0 : Int) <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH12 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  ((days + 1) <= 200)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (n <= (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : ((0 : Int) <= days)) (PreH7 : (days <= 200)) (PreH8 : ((0 : Int) <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH11 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre days) ”
  &&  emp
) \/
(
forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (n <= (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : ((0 : Int) <= days)) (PreH7 : (days <= 200)) (PreH8 : ((0 : Int) <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH11 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre days) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (n : Int) (days : Int) (PreH1 : (n <= (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : ((0 : Int) <= days)) (PreH7 : (days <= 200)) (PreH8 : ((0 : Int) <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (Z.quot days m_pre)) - days))) (PreH11 : forall (d : Int) , (((1 <= d) ∧ (d <= days)) -> (((n_pre + (Z.quot (d - 1) m_pre)) - (d - 1)) > (0 : Int)))) ,
  (Spec n_pre m_pre days)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_return_wit_1 : solver_return_wit_1

end Codeforces.examples_shard01.P011_460A_vasya_and_socks.lean.groundtruth.P011_460A_vasya_and_socks_goal
