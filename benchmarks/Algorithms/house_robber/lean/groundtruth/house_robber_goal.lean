import SimpleC.SL.SeparationLogic

import Algorithms.house_robber.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.house_robber.lean.groundtruth.house_robber_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance house_robber_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def rob_safety_wit_1 : Prop :=
  forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "prev2" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rob_safety_wit_2 : Prop :=
  forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "prev1" ) )) # Int |->_)
  ** ((( &( "prev2" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rob_safety_wit_3 : Prop :=
  forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "prev1" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "prev2" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rob_safety_wit_4 : Prop :=
  forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : ((0 : Int) <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
  ** ((( &( "take" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev2" ) )) # Int |-> (prev2))
  ** ((( &( "prev1" ) )) # Int |-> (prev1))
|--
  “ ((prev2 + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (prev2 + (Znth i l (0 : Int)))) ”

noncomputable def rob_safety_wit_5 : Prop :=
  forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (take : Int) (prev2 : Int) (skip : Int) (prev1 : Int) (cur : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l (0 : Int))))) (PreH8 : (skip = prev1)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : ((0 : Int) <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1) prev1 cur)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full nums_pre n_pre l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev2" ) )) # Int |-> (prev1))
  ** ((( &( "prev1" ) )) # Int |-> (cur))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def rob_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ (HouseRobberDPState l (0 : Int) (0 : Int) (0 : Int)) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  emp
)

noncomputable def rob_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  (HouseRobberDPState l (0 : Int) (0 : Int) (0 : Int))

noncomputable def rob_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def rob_entail_wit_2_1 : Prop :=
  (
forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((prev2 + (Znth i l (0 : Int))) = (prev2 + (Znth i l (0 : Int)))) ” &&
  “ (prev1 = prev1) ” &&
  “ ((0 : Int) <= prev2) ” &&
  “ (prev2 <= 1000000000) ” &&
  “ ((0 : Int) <= prev1) ” &&
  “ (prev1 <= 1000000000) ” &&
  “ ((0 : Int) <= (prev2 + (Znth i l (0 : Int)))) ” &&
  “ ((prev2 + (Znth i l (0 : Int))) <= 1000000000) ” &&
  “ (HouseRobberDPState l (i + 1) prev1 (prev2 + (Znth i l (0 : Int)))) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1) prev1 (prev2 + (Znth i l (0 : Int)))) ” &&
  “ ((prev2 + (Znth i l (0 : Int))) <= 1000000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  emp
)

noncomputable def rob_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  (HouseRobberDPState l (i + 1) prev1 (prev2 + (Znth i l (0 : Int))))

noncomputable def rob_entail_wit_2_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  ((prev2 + (Znth i l (0 : Int))) <= 1000000000)

noncomputable def rob_entail_wit_2_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def rob_entail_wit_2_2 : Prop :=
  (
forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((prev2 + (Znth i l (0 : Int))) = (prev2 + (Znth i l (0 : Int)))) ” &&
  “ (prev1 = prev1) ” &&
  “ ((0 : Int) <= prev2) ” &&
  “ (prev2 <= 1000000000) ” &&
  “ ((0 : Int) <= prev1) ” &&
  “ (prev1 <= 1000000000) ” &&
  “ ((0 : Int) <= prev1) ” &&
  “ (prev1 <= 1000000000) ” &&
  “ (HouseRobberDPState l (i + 1) prev1 prev1) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1) prev1 prev1) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  emp
)

noncomputable def rob_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  (HouseRobberDPState l (i + 1) prev1 prev1)

noncomputable def rob_entail_wit_2_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def rob_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (take : Int) (prev2 : Int) (skip : Int) (prev1 : Int) (cur : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l (0 : Int))))) (PreH8 : (skip = prev1)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : ((0 : Int) <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1) prev1 cur)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= prev1) ” &&
  “ (prev1 <= 1000000000) ” &&
  “ ((0 : Int) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ (HouseRobberDPState l (i + 1) prev1 cur) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (take : Int) (prev2 : Int) (skip : Int) (prev1 : Int) (cur : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l (0 : Int))))) (PreH8 : (skip = prev1)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : ((0 : Int) <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1) prev1 cur)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ”
  &&  emp
)

noncomputable def rob_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (take : Int) (prev2 : Int) (skip : Int) (prev1 : Int) (cur : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l (0 : Int))) ∧ ((Znth k_2 l (0 : Int)) <= 10000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l (0 : Int))))) (PreH8 : (skip = prev1)) (PreH9 : ((0 : Int) <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : ((0 : Int) <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : ((0 : Int) <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1) prev1 cur)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))

noncomputable def rob_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : ((0 : Int) <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ (HouseRobberAnswer l prev1) ” &&
  “ ((0 : Int) <= prev1) ” &&
  “ (prev1 <= 1000000000) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : ((0 : Int) <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1)) ,
  TT && emp 
|--
  “ (HouseRobberAnswer l prev1) ”
  &&  emp
)

noncomputable def rob_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : ((0 : Int) <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1)) ,
  (HouseRobberAnswer l prev1)

noncomputable def rob_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (nums_pre : Int) (l : (List Int)) (prev1 : Int) (prev2 : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : ((0 : Int) <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l (0 : Int))) ∧ ((Znth k l (0 : Int)) <= 10000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= prev2) ” &&
  “ (prev2 <= 1000000000) ” &&
  “ ((0 : Int) <= prev1) ” &&
  “ (prev1 <= 1000000000) ” &&
  “ (HouseRobberDPState l i prev2 prev1) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) n_pre l)


structure VC_Correct : Type where
  proof_of_rob_safety_wit_1 : rob_safety_wit_1
  proof_of_rob_safety_wit_2 : rob_safety_wit_2
  proof_of_rob_safety_wit_3 : rob_safety_wit_3
  proof_of_rob_safety_wit_4 : rob_safety_wit_4
  proof_of_rob_safety_wit_5 : rob_safety_wit_5
  proof_of_rob_partial_solve_wit_1 : rob_partial_solve_wit_1
  proof_of_rob_entail_wit_1 : rob_entail_wit_1
  proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1
  proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2
  proof_of_rob_entail_wit_3 : rob_entail_wit_3
  proof_of_rob_return_wit_1 : rob_return_wit_1

end Algorithms.house_robber.lean.groundtruth.house_robber_goal
