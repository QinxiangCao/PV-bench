import SimpleC.SL.SeparationLogic

import Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.groundtruth.P021_2030C_a_true_battle_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance P021_2030C_a_true_battle_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH5 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH6 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre - 1))) (PreH9 : (NoAdjacentOnesBefore values i)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH5 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH6 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre - 1))) (PreH9 : (NoAdjacentOnesBefore values i)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH6 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH7 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (n_pre - 1))) (PreH10 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH6 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH7 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (n_pre - 1))) (PreH10 : (NoAdjacentOnesBefore values i)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 200000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49))) ” &&
  “ ((Znth (0 : Int) values (0 : Int)) ≠ 49) ” &&
  “ ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ (NoAdjacentOnesBefore values (0 : Int)) ”
  &&  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  TT && emp 
|--
  “ (NoAdjacentOnesBefore values (0 : Int)) ” &&
  “ ((Znth (n_pre - 1) values (0 : Int)) ≠ 49) ” &&
  “ ((Znth (0 : Int) values (0 : Int)) ≠ 49) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (NoAdjacentOnesBefore values (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  ((Znth (n_pre - 1) values (0 : Int)) ≠ 49)

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  ((Znth (0 : Int) values (0 : Int)) ≠ 49)

noncomputable def solver_entail_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 200000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49))) ” &&
  “ ((Znth (0 : Int) values (0 : Int)) ≠ 49) ” &&
  “ ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre - 1)) ” &&
  “ (NoAdjacentOnesBefore values (i + 1)) ”
  &&  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  TT && emp 
|--
  “ (NoAdjacentOnesBefore values (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  (NoAdjacentOnesBefore values (i + 1))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 200000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49))) ” &&
  “ ((Znth (0 : Int) values (0 : Int)) ≠ 49) ” &&
  “ ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre - 1)) ” &&
  “ (NoAdjacentOnesBefore values (i + 1)) ”
  &&  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  TT && emp 
|--
  “ (NoAdjacentOnesBefore values (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  (NoAdjacentOnesBefore values (i + 1))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH6 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH7 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (n_pre - 1))) (PreH10 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (Spec values (0 : Int)) ”
  &&  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH6 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH7 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (n_pre - 1))) (PreH10 : (NoAdjacentOnesBefore values i)) ,
  TT && emp 
|--
  “ (Spec values (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH6 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH7 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (n_pre - 1))) (PreH10 : (NoAdjacentOnesBefore values i)) ,
  (Spec values (0 : Int))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (Spec values 1) ”
  &&  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  TT && emp 
|--
  “ (Spec values 1) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH3 : ((i + 1) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH8 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH9 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre - 1))) (PreH12 : (NoAdjacentOnesBefore values i)) ,
  (Spec values 1)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (Spec values 1) ”
  &&  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  TT && emp 
|--
  “ (Spec values 1) ”
  &&  emp
)

noncomputable def solver_return_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (Spec values 1)

noncomputable def solver_return_wit_4 : Prop :=
  (
forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (Spec values 1) ”
  &&  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  TT && emp 
|--
  “ (Spec values 1) ”
  &&  emp
)

noncomputable def solver_return_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (PreH1 : ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (Spec values 1)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 200000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49))) ”
  &&  (((s_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre (0 : Int) (0 : Int) (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (PreH1 : ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49)))) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((Znth (0 : Int) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 49) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 200000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> (((Znth i values (0 : Int)) = 48) ∨ ((Znth i values (0 : Int)) = 49))) ”
  &&  (((s_pre + ((n_pre - 1) * sizeof(CHAR)))) # Char |-> ((Znth (n_pre - 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre (n_pre - 1) (0 : Int) (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH6 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH7 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (n_pre - 1))) (PreH10 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i + 1) < n_pre) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 200000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49))) ” &&
  “ ((Znth (0 : Int) values (0 : Int)) ≠ 49) ” &&
  “ ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (NoAdjacentOnesBefore values i) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (s_pre : Int) (values : (List Int)) (i : Int) (PreH1 : ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49)) (PreH2 : ((i + 1) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49)))) (PreH7 : ((Znth (0 : Int) values (0 : Int)) ≠ 49)) (PreH8 : ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre - 1))) (PreH11 : (NoAdjacentOnesBefore values i)) ,
  (charArray.full s_pre (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((Znth i (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 49) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 200000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> (((Znth k values (0 : Int)) = 48) ∨ ((Znth k values (0 : Int)) = 49))) ” &&
  “ ((Znth (0 : Int) values (0 : Int)) ≠ 49) ” &&
  “ ((Znth ((Zlength (values)) - 1) values (0 : Int)) ≠ 49) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (NoAdjacentOnesBefore values i) ”
  &&  (((s_pre + ((i + 1) * sizeof(CHAR)))) # Char |-> ((Znth (i + 1) (values ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre (i + 1) (0 : Int) (n_pre + 1) (values ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)


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
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_return_wit_4 : solver_return_wit_4

end Codeforces.examples_shard00.P021_2030C_a_true_battle.lean.groundtruth.P021_2030C_a_true_battle_goal
