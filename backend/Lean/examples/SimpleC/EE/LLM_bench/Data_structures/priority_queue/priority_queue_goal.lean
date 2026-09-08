import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance priority_queue_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def push_safety_wit_1 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written : (List Int)) (child : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource written S_before n_pre x_pre)) (PreH6 : (PushLoopState written current n_pre child x_pre)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full heap_pre (n_pre + 1) current)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def push_safety_wit_2 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre)) (PreH7 : (PushLoopState written current n_pre child x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full heap_pre (n_pre + 1) current)
|--
  “ (((child - 1) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def push_safety_wit_3 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre)) (PreH7 : (PushLoopState written current n_pre child x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full heap_pre (n_pre + 1) current)
|--
  “ ((child - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (child - 1)) ”

noncomputable def push_safety_wit_4 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre)) (PreH7 : (PushLoopState written current n_pre child x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full heap_pre (n_pre + 1) current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def push_safety_wit_5 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre)) (PreH7 : (PushLoopState written current n_pre child x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full heap_pre (n_pre + 1) current)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def push_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (PreH1 : (n_pre < heap_capacity)) ,
  (store_heap heap_pre S_before n_pre)
  ** (intArray.undef_seg heap_pre n_pre (n_pre + 1))
|--
  EX base : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (heap_representation S_before base n_pre) ”
  &&  (intArray.full heap_pre n_pre base)
  ** (intArray.undef_seg heap_pre n_pre (n_pre + 1))
) \/
(
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (PreH1 : (n_pre < heap_capacity)) ,
  (store_heap heap_pre S_before n_pre)
|--
  EX base : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (heap_representation S_before base n_pre) ”
  &&  (intArray.full heap_pre n_pre base)
)

noncomputable def push_entail_wit_2 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before base n_pre)) ,
  (intArray.full heap_pre (n_pre + 1) (base ++ (x_pre :: (@List.nil Int))))
|--
  EX written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written written n_pre n_pre x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) written)
) \/
(
forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before base n_pre)) ,
  TT && emp 
|--
  “ (PushLoopState (base ++ (x_pre :: (@List.nil Int))) (base ++ (x_pre :: (@List.nil Int))) n_pre n_pre x_pre) ” &&
  “ (PushSource (base ++ (x_pre :: (@List.nil Int))) S_before n_pre x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before base n_pre)) ,
  (PushLoopState (base ++ (x_pre :: (@List.nil Int))) (base ++ (x_pre :: (@List.nil Int))) n_pre n_pre x_pre)

noncomputable def push_entail_wit_2_split_goal_2 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before base n_pre)) ,
  (PushSource (base ++ (x_pre :: (@List.nil Int))) S_before n_pre x_pre)

noncomputable def push_entail_wit_3 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (PushSource written_2 S_before n_pre x_pre)) (PreH4 : (PushLoopState written_2 written_2 n_pre n_pre x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) written_2)
|--
  EX current : (List Int), EX written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre n_pre x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) current)
) \/
(
forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (PushSource written_2 S_before n_pre x_pre)) (PreH4 : (PushLoopState written_2 written_2 n_pre n_pre x_pre)) ,
  TT && emp 
|--
  EX written : (List Int),
  “ (n_pre <= n_pre) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written written_2 n_pre n_pre x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_4 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current_2 : (List Int)) (written_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written_2 S_before n_pre x_pre)) (PreH7 : (PushLoopState written_2 current_2 n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current_2)
|--
  EX current : (List Int), EX written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((Z.quot (child - 1) 2) <= n_pre) ” &&
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre child x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) current)
) \/
(
forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (current_2 : (List Int)) (written_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written_2 S_before n_pre x_pre)) (PreH7 : (PushLoopState written_2 current_2 n_pre child x_pre)) ,
  TT && emp 
|--
  EX written : (List Int),
  “ ((0 : Int) < child) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((Z.quot (child - 1) 2) <= n_pre) ” &&
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current_2 n_pre child x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_5 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current_2 (0 : Int)) >= (Znth child current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushLoopState written_2 current_2 n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current_2)
|--
  EX written : (List Int), EX current : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent current (0 : Int)) >= (Znth child current (0 : Int))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushResult S_before current n_pre x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) current)
) \/
(
forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current_2 (0 : Int)) >= (Znth child current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushLoopState written_2 current_2 n_pre child x_pre)) ,
  TT && emp 
|--
  “ (PushResult S_before current_2 n_pre x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_5_split_goal_1 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current_2 (0 : Int)) >= (Znth child current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushLoopState written_2 current_2 n_pre child x_pre)) ,
  (PushResult S_before current_2 n_pre x_pre)

noncomputable def push_entail_wit_6 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current (0 : Int)) < (Znth child current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushLoopState written_2 current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) (replace_Znth (child) ((Znth parent current (0 : Int))) ((replace_Znth (parent) ((Znth child current (0 : Int))) (current)))))
|--
  EX written : (List Int), EX current_2 : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent current (0 : Int)) = (Znth child current_2 (0 : Int))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current_2 n_pre parent x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) current_2)
) \/
(
forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current (0 : Int)) < (Znth child current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushLoopState written_2 current n_pre child x_pre)) ,
  TT && emp 
|--
  EX written : (List Int),
  “ ((Znth (heap_parent (child)) current (0 : Int)) = (Znth child (replace_Znth (child) ((Znth (heap_parent (child)) current (0 : Int))) ((replace_Znth ((heap_parent (child))) ((Znth child current (0 : Int))) (current)))) (0 : Int))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written (replace_Znth (child) ((Znth (heap_parent (child)) current (0 : Int))) ((replace_Znth ((heap_parent (child))) ((Znth child current (0 : Int))) (current)))) n_pre (heap_parent (child)) x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_7 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current_2 : (List Int)) (child : Int) (parent : Int) (tmp : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (tmp = (Znth child current_2 (0 : Int)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushLoopState written_2 current_2 n_pre parent x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current_2)
|--
  EX current : (List Int), EX written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent <= n_pre) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre parent x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) current)
) \/
(
forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current_2 : (List Int)) (child : Int) (parent : Int) (tmp : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (tmp = (Znth child current_2 (0 : Int)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushLoopState written_2 current_2 n_pre parent x_pre)) ,
  TT && emp 
|--
  EX written : (List Int),
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current_2 n_pre (heap_parent (child)) x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_8_1 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written_2 : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written_2 S_before n_pre x_pre)) (PreH7 : (PushLoopState written_2 current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current)
|--
  EX result : (List Int), EX written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) <= child) ” &&
  “ (child <= n_pre) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushResult S_before result n_pre x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) result)
) \/
(
forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written_2 : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written_2 S_before n_pre x_pre)) (PreH7 : (PushLoopState written_2 current n_pre child x_pre)) ,
  TT && emp 
|--
  “ (PushResult S_before current n_pre x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_8_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (written_2 : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written_2 S_before n_pre x_pre)) (PreH7 : (PushLoopState written_2 current n_pre child x_pre)) ,
  (PushResult S_before current n_pre x_pre)

noncomputable def push_entail_wit_8_2 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written_2 : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent current (0 : Int)) >= (Znth child current (0 : Int)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre)) (PreH11 : (PushResult S_before current n_pre x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current)
|--
  EX result : (List Int), EX written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) <= child) ” &&
  “ (child <= n_pre) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushResult S_before result n_pre x_pre) ”
  &&  (intArray.full heap_pre (n_pre + 1) result)

noncomputable def push_entail_wit_9 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (result : (List Int)) (child : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource written S_before n_pre x_pre)) (PreH6 : (PushResult S_before result n_pre x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) result)
|--
  “ ((0 : Int) <= child) ” &&
  “ (child <= n_pre) ”
  &&  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1))
) \/
(
forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (result : (List Int)) (child : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource written S_before n_pre x_pre)) (PreH6 : (PushResult S_before result n_pre x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) result)
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1))
)

noncomputable def push_entail_wit_9_split_goal_spatial : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (result : (List Int)) (child : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource written S_before n_pre x_pre)) (PreH6 : (PushResult S_before result n_pre x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) result)
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1))

noncomputable def push_return_wit_1 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (child : Int) (PreH1 : ((0 : Int) <= child)) (PreH2 : (child <= n_pre)) ,
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1))
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1))

noncomputable def push_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before base n_pre)) ,
  (intArray.full heap_pre n_pre base)
  ** (intArray.undef_seg heap_pre n_pre (n_pre + 1))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (heap_representation S_before base n_pre) ”
  &&  (((heap_pre + (n_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.full heap_pre n_pre base)

noncomputable def push_partial_solve_wit_2 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource written S_before n_pre x_pre)) (PreH10 : (PushLoopState written current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre child x_pre) ”
  &&  (((heap_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent current (0 : Int))))
  ** (intArray.missing_i heap_pre parent (0 : Int) (n_pre + 1) current)

noncomputable def push_partial_solve_wit_3 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource written S_before n_pre x_pre)) (PreH10 : (PushLoopState written current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre child x_pre) ”
  &&  (((heap_pre + (child * sizeof(INT)))) # Int |-> ((Znth child current (0 : Int))))
  ** (intArray.missing_i heap_pre child (0 : Int) (n_pre + 1) current)

noncomputable def push_partial_solve_wit_4 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current (0 : Int)) < (Znth child current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre)) (PreH11 : (PushLoopState written current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current)
|--
  “ ((Znth parent current (0 : Int)) < (Znth child current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre child x_pre) ”
  &&  (((heap_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent current (0 : Int))))
  ** (intArray.missing_i heap_pre parent (0 : Int) (n_pre + 1) current)

noncomputable def push_partial_solve_wit_5 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current (0 : Int)) < (Znth child current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre)) (PreH11 : (PushLoopState written current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current)
|--
  “ ((Znth parent current (0 : Int)) < (Znth child current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre child x_pre) ”
  &&  (((heap_pre + (child * sizeof(INT)))) # Int |-> ((Znth child current (0 : Int))))
  ** (intArray.missing_i heap_pre child (0 : Int) (n_pre + 1) current)

noncomputable def push_partial_solve_wit_6 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current (0 : Int)) < (Znth child current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre)) (PreH11 : (PushLoopState written current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) current)
|--
  “ ((Znth parent current (0 : Int)) < (Znth child current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre child x_pre) ”
  &&  (((heap_pre + (parent * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i heap_pre parent (0 : Int) (n_pre + 1) current)

noncomputable def push_partial_solve_wit_7 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (written : (List Int)) (current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent current (0 : Int)) < (Znth child current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre)) (PreH11 : (PushLoopState written current n_pre child x_pre)) ,
  (intArray.full heap_pre (n_pre + 1) (replace_Znth (parent) ((Znth child current (0 : Int))) (current)))
|--
  “ ((Znth parent current (0 : Int)) < (Znth child current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource written S_before n_pre x_pre) ” &&
  “ (PushLoopState written current n_pre child x_pre) ”
  &&  (((heap_pre + (child * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i heap_pre child (0 : Int) (n_pre + 1) (replace_Znth (parent) ((Znth child current (0 : Int))) (current)))

noncomputable def build_safety_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full heap_pre n_pre input)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_2 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full heap_pre n_pre input)
|--
  “ False ”

noncomputable def build_safety_wit_3 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState (multiset_insert (S_prefix) (x)) input (i + 1))) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (store_heap heap_pre (multiset_insert (S_prefix) (x)) (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_entail_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (intArray.full heap_pre n_pre input)
|--
  (“ (n_pre = (0 : Int)) ” &&
  “ (1 = 1) ” &&
  “ ((Zlength (input)) = n_pre) ”
  &&  (intArray.full heap_pre n_pre input))
  ||
  (EX S_prefix : (multiset Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix input 1) ”
  &&  (store_heap heap_pre S_prefix 1)
  ** (intArray.seg heap_pre 1 n_pre (sublist (1) (n_pre) (input))))

noncomputable def build_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix_2 : (multiset Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i)) ,
  (intArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)))
  ** (store_heap heap_pre S_prefix_2 i)
|--
  EX S_prefix : (multiset Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth (i - i) (sublist (i) (n_pre) (input)) (0 : Int)) = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix input i) ”
  &&  (store_heap heap_pre S_prefix i)
  ** (intArray.undef_seg heap_pre i (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
) \/
(
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix_2 : (multiset Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i)) ,
  (intArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)))
  ** (store_heap heap_pre S_prefix_2 i)
|--
  EX S_prefix : (multiset Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth (i - i) (sublist (i) (n_pre) (input)) (0 : Int)) = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix input i) ”
  &&  (store_heap heap_pre S_prefix i)
  ** (intArray.undef_seg heap_pre i (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
)

noncomputable def build_entail_wit_3 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix_2 : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i)) ,
  (store_heap heap_pre (multiset_insert (S_prefix_2) (x)) (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  EX S_prefix : (multiset Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix input i) ”
  &&  (store_heap heap_pre (multiset_insert (S_prefix) (x)) (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))

noncomputable def build_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix_2 : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i)) ,
  (store_heap heap_pre (multiset_insert (S_prefix_2) (x)) (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  EX S_prefix : (multiset Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState (multiset_insert (S_prefix) (x)) input (i + 1)) ”
  &&  (store_heap heap_pre (multiset_insert (S_prefix) (x)) (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
) \/
(
forall (n_pre : Int) (input : (List Int)) (S_prefix_2 : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i)) ,
  TT && emp 
|--
  “ (BuildPrefixState (multiset_insert (S_prefix_2) (x)) input (i + 1)) ”
  &&  emp
)

noncomputable def build_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (S_prefix_2 : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i)) ,
  (BuildPrefixState (multiset_insert (S_prefix_2) (x)) input (i + 1))

noncomputable def build_entail_wit_5 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix_2 : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState (multiset_insert (S_prefix_2) (x)) input (i + 1))) ,
  (store_heap heap_pre (multiset_insert (S_prefix_2) (x)) (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  EX S_prefix : (multiset Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix input (i + 1)) ”
  &&  (store_heap heap_pre S_prefix (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))

noncomputable def build_entail_wit_6_1 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (intArray.full heap_pre n_pre input)
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (intArray.full heap_pre n_pre input)
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre)
)

noncomputable def build_entail_wit_6_1_split_goal_spatial : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (intArray.full heap_pre n_pre input)
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre)

noncomputable def build_entail_wit_6_2 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix : (multiset Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i)) ,
  (store_heap heap_pre S_prefix i)
  ** (intArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix : (multiset Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i)) ,
  (store_heap heap_pre S_prefix i)
  ** (intArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre)
)

noncomputable def build_entail_wit_6_2_split_goal_spatial : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix : (multiset Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i)) ,
  (store_heap heap_pre S_prefix i)
  ** (intArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre)

noncomputable def build_return_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) ,
  (store_heap heap_pre (list_to_multiset (input)) n_pre)
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre)

noncomputable def build_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix : (multiset Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i)) ,
  (store_heap heap_pre S_prefix i)
  ** (intArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix input i) ”
  &&  (((heap_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - i) (sublist (i) (n_pre) (input)) (0 : Int))))
  ** (intArray.missing_i heap_pre i i n_pre (sublist (i) (n_pre) (input)))
  ** (store_heap heap_pre S_prefix i)

noncomputable def build_partial_solve_wit_2_pure : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (store_heap heap_pre S_prefix i)
  ** (intArray.undef_seg heap_pre i (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  “ (i < heap_capacity) ”

noncomputable def build_partial_solve_wit_2_aux : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (S_prefix : (multiset Int)) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i)) ,
  (store_heap heap_pre S_prefix i)
  ** (intArray.undef_seg heap_pre i (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  “ (i < heap_capacity) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix input i) ”
  &&  (store_heap heap_pre S_prefix i)
  ** (intArray.undef_seg heap_pre i (i + 1))
  ** (intArray.seg heap_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))

noncomputable def build_partial_solve_wit_2 : Prop := build_partial_solve_wit_2_pure -> build_partial_solve_wit_2_aux

noncomputable def pop_safety_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before n_pre)) (PreH4 : (PrefixMaximum before n_pre (Znth (0 : Int) before (0 : Int)))) (PreH5 : ((Znth (0 : Int) before (0 : Int)) = (multiset_max (S_before)))) (PreH6 : (multiset_maximum S_before (Znth (0 : Int) before (0 : Int)))) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full heap_pre n_pre before)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_2 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** (intArray.full heap_pre n_pre before)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_3 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** (intArray.full heap_pre n_pre before)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_4 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** (intArray.full heap_pre n_pre before)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_5 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** (intArray.full heap_pre n_pre before)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_6 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : (PopLoopState before current n_pre (0 : Int))) ,
  ((( &( "idx" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** (intArray.full heap_pre n_pre current)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_7 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : ((0 : Int) <= ((idx * 2) + 1))) (PreH11 : (((idx * 2) + 1) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_8 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : ((0 : Int) <= ((idx * 2) + 1))) (PreH11 : (((idx * 2) + 1) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (((idx * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((idx * 2) + 1)) ”

noncomputable def pop_safety_wit_9 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : ((0 : Int) <= ((idx * 2) + 1))) (PreH11 : (((idx * 2) + 1) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ ((idx * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (idx * 2)) ”

noncomputable def pop_safety_wit_10 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : ((0 : Int) <= ((idx * 2) + 1))) (PreH11 : (((idx * 2) + 1) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def pop_safety_wit_11 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : ((0 : Int) <= ((idx * 2) + 1))) (PreH11 : (((idx * 2) + 1) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_12 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : ((0 : Int) <= ((idx * 2) + 1))) (PreH11 : (((idx * 2) + 1) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_13 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (((idx * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((idx * 2) + 1)) ”

noncomputable def pop_safety_wit_14 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ ((idx * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (idx * 2)) ”

noncomputable def pop_safety_wit_15 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def pop_safety_wit_16 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_17 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> (((idx * 2) + 1)))
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ ((((idx * 2) + 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((idx * 2) + 1) + 1)) ”

noncomputable def pop_safety_wit_18 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current : (List Int)) (idx : Int) (before : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> (((idx * 2) + 1)))
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_19 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : (largest = left)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (left < (n_pre - 1))) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right <= (n_pre - 1))) (PreH17 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "largest" ) )) # Int |-> (largest))
  ** (intArray.full heap_pre n_pre current)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_20 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : (largest = left)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (left < (n_pre - 1))) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right <= (n_pre - 1))) (PreH17 : (PopLoopState before current n_pre idx)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "largest" ) )) # Int |-> (largest))
  ** (intArray.full heap_pre n_pre current)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (PreH1 : (1 <= n_pre)) ,
  (store_heap heap_pre S_before n_pre)
|--
  EX before : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before (0 : Int))) ” &&
  “ ((Znth (0 : Int) before (0 : Int)) = (multiset_max (S_before))) ” &&
  “ (multiset_maximum S_before (Znth (0 : Int) before (0 : Int))) ”
  &&  (intArray.full heap_pre n_pre before)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (PreH1 : (1 <= n_pre)) ,
  (store_heap heap_pre S_before n_pre)
|--
  EX before : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before (0 : Int))) ” &&
  “ ((Znth (0 : Int) before (0 : Int)) = (multiset_max (S_before))) ” &&
  “ (multiset_maximum S_before (Znth (0 : Int) before (0 : Int))) ”
  &&  (intArray.full heap_pre n_pre before)
)

noncomputable def pop_entail_wit_2 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before n_pre)) (PreH4 : (PrefixMaximum before n_pre (Znth (0 : Int) before (0 : Int)))) (PreH5 : ((Znth (0 : Int) before (0 : Int)) = (multiset_max (S_before)))) (PreH6 : (multiset_maximum S_before (Znth (0 : Int) before (0 : Int)))) ,
  (intArray.full heap_pre n_pre before)
|--
  EX before_2 : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Znth (0 : Int) before (0 : Int)) = (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ ((Znth (0 : Int) before (0 : Int)) = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before_2 n_pre) ” &&
  “ (PrefixMaximum before_2 n_pre (Znth (0 : Int) before (0 : Int))) ” &&
  “ (multiset_maximum S_before (Znth (0 : Int) before (0 : Int))) ”
  &&  (intArray.full heap_pre n_pre before_2)

noncomputable def pop_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  (intArray.full heap_pre n_pre before)
|--
  “ (n_pre = 1) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (multiset_maximum S_before ret) ”
  &&  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (0 : Int))
  ** (intArray.undef_seg heap_pre (0 : Int) 1)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  (intArray.full heap_pre n_pre before)
|--
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (0 : Int))
  ** (intArray.undef_seg heap_pre (0 : Int) 1)
)

noncomputable def pop_entail_wit_3_split_goal_spatial : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  (intArray.full heap_pre n_pre before)
|--
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (0 : Int))
  ** (intArray.undef_seg heap_pre (0 : Int) 1)

noncomputable def pop_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (ret : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  (intArray.full heap_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_2 (0 : Int))) (before_2)))
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ (PopLoopState before current n_pre (0 : Int)) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (ret : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ (PopLoopState before (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_2 (0 : Int))) (before_2)) n_pre (0 : Int)) ”
  &&  emp
)

noncomputable def pop_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : (PopLoopState before_2 current_2 n_pre (0 : Int))) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (((0 : Int) * 2) + 1)) ” &&
  “ ((((0 : Int) * 2) + 1) <= INT_MAX) ” &&
  “ (PopLoopState before current n_pre (0 : Int)) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : (PopLoopState before_2 current_2 n_pre (0 : Int))) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (((0 : Int) * 2) + 1)) ” &&
  “ ((((0 : Int) * 2) + 1) <= INT_MAX) ” &&
  “ (PopLoopState before current_2 n_pre (0 : Int)) ”
  &&  emp
)

noncomputable def pop_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current_2 : (List Int)) (idx : Int) (before_2 : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before_2 current_2 n_pre idx)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (((idx * 2) + 1) = ((idx * 2) + 1)) ” &&
  “ ((((idx * 2) + 1) + 1) = (((idx * 2) + 1) + 1)) ” &&
  “ (((idx * 2) + 1) = ((idx * 2) + 1)) ” &&
  “ ((0 : Int) <= ((idx * 2) + 1)) ” &&
  “ (((idx * 2) + 1) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (((idx * 2) + 1) + 1)) ” &&
  “ ((((idx * 2) + 1) + 1) <= (n_pre - 1)) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (current_2 : (List Int)) (idx : Int) (before_2 : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before_2 current_2 n_pre idx)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ ((0 : Int) <= (((idx * 2) + 1) + 1)) ” &&
  “ ((((idx * 2) + 1) + 1) <= (n_pre - 1)) ” &&
  “ (PopLoopState before current_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_7_1 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth left current_2 (0 : Int)) < (Znth right current_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before_2 n_pre)) (PreH8 : (PrefixMaximum before_2 n_pre ret)) (PreH9 : (multiset_maximum S_before ret)) (PreH10 : ((0 : Int) <= idx)) (PreH11 : (idx < (n_pre - 1))) (PreH12 : (left = ((idx * 2) + 1))) (PreH13 : (right = (left + 1))) (PreH14 : (largest = left)) (PreH15 : ((0 : Int) <= left)) (PreH16 : (left < (n_pre - 1))) (PreH17 : ((0 : Int) <= right)) (PreH18 : (right <= (n_pre - 1))) (PreH19 : (PopLoopState before_2 current_2 n_pre idx)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx right) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth left current_2 (0 : Int)) < (Znth right current_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before_2 n_pre)) (PreH8 : (PrefixMaximum before_2 n_pre ret)) (PreH9 : (multiset_maximum S_before ret)) (PreH10 : ((0 : Int) <= idx)) (PreH11 : (idx < (n_pre - 1))) (PreH12 : (left = ((idx * 2) + 1))) (PreH13 : (right = (left + 1))) (PreH14 : (largest = left)) (PreH15 : ((0 : Int) <= left)) (PreH16 : (left < (n_pre - 1))) (PreH17 : ((0 : Int) <= right)) (PreH18 : (right <= (n_pre - 1))) (PreH19 : (PopLoopState before_2 current_2 n_pre idx)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ (PopSelectedChild current_2 (n_pre - 1) idx (left + 1)) ” &&
  “ (PopLoopState before current_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_7_2 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (right >= (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : (largest = left)) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (n_pre - 1))) (PreH16 : ((0 : Int) <= right)) (PreH17 : (right <= (n_pre - 1))) (PreH18 : (PopLoopState before_2 current_2 n_pre idx)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (right >= (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : (largest = left)) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (n_pre - 1))) (PreH16 : ((0 : Int) <= right)) (PreH17 : (right <= (n_pre - 1))) (PreH18 : (PopLoopState before_2 current_2 n_pre idx)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ (PopSelectedChild current_2 (n_pre - 1) idx left) ” &&
  “ (PopLoopState before current_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_7_3 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth left current_2 (0 : Int)) >= (Znth right current_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before_2 n_pre)) (PreH8 : (PrefixMaximum before_2 n_pre ret)) (PreH9 : (multiset_maximum S_before ret)) (PreH10 : ((0 : Int) <= idx)) (PreH11 : (idx < (n_pre - 1))) (PreH12 : (left = ((idx * 2) + 1))) (PreH13 : (right = (left + 1))) (PreH14 : (largest = left)) (PreH15 : ((0 : Int) <= left)) (PreH16 : (left < (n_pre - 1))) (PreH17 : ((0 : Int) <= right)) (PreH18 : (right <= (n_pre - 1))) (PreH19 : (PopLoopState before_2 current_2 n_pre idx)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth left current_2 (0 : Int)) >= (Znth right current_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before_2 n_pre)) (PreH8 : (PrefixMaximum before_2 n_pre ret)) (PreH9 : (multiset_maximum S_before ret)) (PreH10 : ((0 : Int) <= idx)) (PreH11 : (idx < (n_pre - 1))) (PreH12 : (left = ((idx * 2) + 1))) (PreH13 : (right = (left + 1))) (PreH14 : (largest = left)) (PreH15 : ((0 : Int) <= left)) (PreH16 : (left < (n_pre - 1))) (PreH17 : ((0 : Int) <= right)) (PreH18 : (right <= (n_pre - 1))) (PreH19 : (PopLoopState before_2 current_2 n_pre idx)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ (PopSelectedChild current_2 (n_pre - 1) idx left) ” &&
  “ (PopLoopState before current_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current_2 (0 : Int)) >= (Znth largest current_2 (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current_2 (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before_2 current_2 n_pre idx)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (n_pre - 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right <= (n_pre - 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ ((Znth idx current (0 : Int)) >= (Znth largest current (0 : Int))) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopReadyState before current n_pre ret) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current_2 (0 : Int)) >= (Znth largest current_2 (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current_2 (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before_2 current_2 n_pre idx)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ ((0 : Int) <= ((idx * 2) + 1)) ” &&
  “ (((idx * 2) + 1) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= (n_pre - 1)) ” &&
  “ (PopReadyState before current_2 n_pre (Znth (0 : Int) before_2 (0 : Int))) ”
  &&  emp
)

noncomputable def pop_entail_wit_9 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before_2 current n_pre idx)) ,
  (intArray.full heap_pre n_pre (replace_Znth (largest) ((Znth idx current (0 : Int))) ((replace_Znth (idx) ((Znth largest current (0 : Int))) (current)))))
|--
  EX current_2 : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (n_pre - 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right <= (n_pre - 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (idx < largest) ” &&
  “ ((Znth idx current (0 : Int)) = (Znth largest current_2 (0 : Int))) ” &&
  “ (PopLoopState before current_2 n_pre largest) ”
  &&  (intArray.full heap_pre n_pre current_2)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before_2 current n_pre idx)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ ((0 : Int) <= ((idx * 2) + 1)) ” &&
  “ (((idx * 2) + 1) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= (n_pre - 1)) ” &&
  “ (idx < largest) ” &&
  “ ((Znth idx current (0 : Int)) = (Znth largest (replace_Znth (largest) ((Znth idx current (0 : Int))) ((replace_Znth (idx) ((Znth largest current (0 : Int))) (current)))) (0 : Int))) ” &&
  “ (PopLoopState before (replace_Znth (largest) ((Znth idx current (0 : Int))) ((replace_Znth (idx) ((Znth largest current (0 : Int))) (current)))) n_pre largest) ”
  &&  emp
)

noncomputable def pop_entail_wit_10 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (tmp : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : ((0 : Int) <= largest)) (PreH17 : (largest < (n_pre - 1))) (PreH18 : (idx < largest)) (PreH19 : (tmp = (Znth largest current_2 (0 : Int)))) (PreH20 : (PopLoopState before_2 current_2 n_pre largest)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ ((0 : Int) <= ((largest * 2) + 1)) ” &&
  “ (((largest * 2) + 1) <= INT_MAX) ” &&
  “ (PopLoopState before current n_pre largest) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (tmp : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : ((0 : Int) <= largest)) (PreH17 : (largest < (n_pre - 1))) (PreH18 : (idx < largest)) (PreH19 : (tmp = (Znth largest current_2 (0 : Int)))) (PreH20 : (PopLoopState before_2 current_2 n_pre largest)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ ((0 : Int) <= ((largest * 2) + 1)) ” &&
  “ (((largest * 2) + 1) <= INT_MAX) ” &&
  “ (PopLoopState before current_2 n_pre largest) ”
  &&  emp
)

noncomputable def pop_entail_wit_11_1 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (current_2 : (List Int)) (idx : Int) (before_2 : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) >= (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before_2 current_2 n_pre idx)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (PopReadyState before current n_pre ret) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (current_2 : (List Int)) (idx : Int) (before_2 : (List Int)) (ret : Int) (PreH1 : (((idx * 2) + 1) >= (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre)) (PreH7 : (PrefixMaximum before_2 n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : ((0 : Int) <= ((idx * 2) + 1))) (PreH12 : (((idx * 2) + 1) <= INT_MAX)) (PreH13 : (PopLoopState before_2 current_2 n_pre idx)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ (PopReadyState before current_2 n_pre (Znth (0 : Int) before_2 (0 : Int))) ”
  &&  emp
)

noncomputable def pop_entail_wit_11_2 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : ((0 : Int) <= largest)) (PreH17 : (largest < (n_pre - 1))) (PreH18 : ((Znth idx current_2 (0 : Int)) >= (Znth largest current_2 (0 : Int)))) (PreH19 : (PopSelectedChild current_2 (n_pre - 1) idx largest)) (PreH20 : (PopReadyState before_2 current_2 n_pre ret)) ,
  (intArray.full heap_pre n_pre current_2)
|--
  EX current : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (PopReadyState before current n_pre ret) ”
  &&  (intArray.full heap_pre n_pre current)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current_2 : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : ((0 : Int) <= largest)) (PreH17 : (largest < (n_pre - 1))) (PreH18 : ((Znth idx current_2 (0 : Int)) >= (Znth largest current_2 (0 : Int)))) (PreH19 : (PopSelectedChild current_2 (n_pre - 1) idx largest)) (PreH20 : (PopReadyState before_2 current_2 n_pre ret)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ (PopReadyState before current_2 n_pre (Znth (0 : Int) before_2 (0 : Int))) ”
  &&  emp
)

noncomputable def pop_entail_wit_12 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (PopReadyState before_2 current n_pre ret)) ,
  (intArray.full heap_pre n_pre current)
|--
  EX result : (List Int), EX before : (List Int),
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ (PopResult S_before before result n_pre ret) ”
  &&  (intArray.full heap_pre n_pre result)
) \/
(
forall (n_pre : Int) (S_before : (multiset Int)) (before_2 : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before_2 (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before_2 n_pre)) (PreH6 : (PrefixMaximum before_2 n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (PopReadyState before_2 current n_pre ret)) ,
  TT && emp 
|--
  EX before : (List Int),
  “ ((Znth (0 : Int) before_2 (0 : Int)) = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before_2 (0 : Int))) ” &&
  “ (PopResult S_before before current n_pre (Znth (0 : Int) before_2 (0 : Int))) ”
  &&  emp
)

noncomputable def pop_entail_wit_13 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (result : (List Int)) (idx : Int) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((0 : Int) <= idx)) (PreH4 : (idx < (n_pre - 1))) (PreH5 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before n_pre)) (PreH8 : (PrefixMaximum before n_pre ret)) (PreH9 : (multiset_maximum S_before ret)) (PreH10 : (PopResult S_before before result n_pre ret)) ,
  (intArray.full heap_pre n_pre result)
|--
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (multiset_maximum S_before ret) ”
  &&  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))
  ** (intArray.undef_seg heap_pre (n_pre - 1) n_pre)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (result : (List Int)) (idx : Int) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((0 : Int) <= idx)) (PreH4 : (idx < (n_pre - 1))) (PreH5 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before n_pre)) (PreH8 : (PrefixMaximum before n_pre ret)) (PreH9 : (multiset_maximum S_before ret)) (PreH10 : (PopResult S_before before result n_pre ret)) ,
  (intArray.full heap_pre n_pre result)
|--
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))
  ** (intArray.undef_seg heap_pre (n_pre - 1) n_pre)
)

noncomputable def pop_entail_wit_13_split_goal_spatial : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (result : (List Int)) (idx : Int) (ret : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((0 : Int) <= idx)) (PreH4 : (idx < (n_pre - 1))) (PreH5 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before n_pre)) (PreH8 : (PrefixMaximum before n_pre ret)) (PreH9 : (multiset_maximum S_before ret)) (PreH10 : (PopResult S_before before result n_pre ret)) ,
  (intArray.full heap_pre n_pre result)
|--
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))
  ** (intArray.undef_seg heap_pre (n_pre - 1) n_pre)

noncomputable def pop_return_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (idx : Int) (ret : Int) (PreH1 : ((0 : Int) <= idx)) (PreH2 : (idx < (n_pre - 1))) (PreH3 : (ret = (multiset_max (S_before)))) (PreH4 : (multiset_maximum S_before ret)) ,
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))
  ** (intArray.undef_seg heap_pre (n_pre - 1) n_pre)
|--
  “ (ret = (multiset_max (S_before))) ” &&
  “ (multiset_maximum S_before ret) ”
  &&  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))
  ** (intArray.undef_seg heap_pre (n_pre - 1) n_pre)

noncomputable def pop_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (ret : Int) (PreH1 : (n_pre = 1)) (PreH2 : (ret = (multiset_max (S_before)))) (PreH3 : (multiset_maximum S_before ret)) ,
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (0 : Int))
  ** (intArray.undef_seg heap_pre (0 : Int) 1)
|--
  “ (ret = (multiset_max (S_before))) ” &&
  “ (multiset_maximum S_before ret) ”
  &&  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))
  ** (intArray.undef_seg heap_pre (n_pre - 1) n_pre)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (ret : Int) (PreH1 : (n_pre = 1)) (PreH2 : (ret = (multiset_max (S_before)))) (PreH3 : (multiset_maximum S_before ret)) ,
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (0 : Int))
|--
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))
)

noncomputable def pop_return_wit_2_split_goal_spatial : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (ret : Int) (PreH1 : (n_pre = 1)) (PreH2 : (ret = (multiset_max (S_before)))) (PreH3 : (multiset_maximum S_before ret)) ,
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (0 : Int))
|--
  (store_heap heap_pre (multiset_remove (S_before) ((multiset_max (S_before)))) (n_pre - 1))

noncomputable def pop_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before n_pre)) (PreH4 : (PrefixMaximum before n_pre (Znth (0 : Int) before (0 : Int)))) (PreH5 : ((Znth (0 : Int) before (0 : Int)) = (multiset_max (S_before)))) (PreH6 : (multiset_maximum S_before (Znth (0 : Int) before (0 : Int)))) ,
  (intArray.full heap_pre n_pre before)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre (Znth (0 : Int) before (0 : Int))) ” &&
  “ ((Znth (0 : Int) before (0 : Int)) = (multiset_max (S_before))) ” &&
  “ (multiset_maximum S_before (Znth (0 : Int) before (0 : Int))) ”
  &&  (((heap_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) before (0 : Int))))
  ** (intArray.missing_i heap_pre (0 : Int) (0 : Int) n_pre before)

noncomputable def pop_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  (intArray.full heap_pre n_pre before)
|--
  “ (n_pre ≠ 1) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ”
  &&  (((heap_pre + ((n_pre - 1) * sizeof(INT)))) # Int |-> ((Znth (n_pre - 1) before (0 : Int))))
  ** (intArray.missing_i heap_pre (n_pre - 1) (0 : Int) n_pre before)

noncomputable def pop_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (ret : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) ,
  (intArray.full heap_pre n_pre before)
|--
  “ (n_pre ≠ 1) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ”
  &&  (((heap_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i heap_pre (0 : Int) (0 : Int) n_pre before)

noncomputable def pop_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (right < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : (largest = left)) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (n_pre - 1))) (PreH16 : ((0 : Int) <= right)) (PreH17 : (right <= (n_pre - 1))) (PreH18 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre current)
|--
  “ (right < (n_pre - 1)) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ (largest = left) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (n_pre - 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right <= (n_pre - 1)) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (left * sizeof(INT)))) # Int |-> ((Znth left current (0 : Int))))
  ** (intArray.missing_i heap_pre left (0 : Int) n_pre current)

noncomputable def pop_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (right < (n_pre - 1))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : (largest = left)) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (n_pre - 1))) (PreH16 : ((0 : Int) <= right)) (PreH17 : (right <= (n_pre - 1))) (PreH18 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre current)
|--
  “ (right < (n_pre - 1)) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ (largest = left) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (n_pre - 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right <= (n_pre - 1)) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (right * sizeof(INT)))) # Int |-> ((Znth right current (0 : Int))))
  ** (intArray.missing_i heap_pre right (0 : Int) n_pre current)

noncomputable def pop_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : ((0 : Int) <= largest)) (PreH13 : (largest < (n_pre - 1))) (PreH14 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH15 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre current)
|--
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (idx * sizeof(INT)))) # Int |-> ((Znth idx current (0 : Int))))
  ** (intArray.missing_i heap_pre idx (0 : Int) n_pre current)

noncomputable def pop_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre)) (PreH6 : (PrefixMaximum before n_pre ret)) (PreH7 : (multiset_maximum S_before ret)) (PreH8 : ((0 : Int) <= idx)) (PreH9 : (idx < (n_pre - 1))) (PreH10 : (left = ((idx * 2) + 1))) (PreH11 : (right = (left + 1))) (PreH12 : ((0 : Int) <= largest)) (PreH13 : (largest < (n_pre - 1))) (PreH14 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH15 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre current)
|--
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (largest * sizeof(INT)))) # Int |-> ((Znth largest current (0 : Int))))
  ** (intArray.missing_i heap_pre largest (0 : Int) n_pre current)

noncomputable def pop_partial_solve_wit_8 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre current)
|--
  “ ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (idx * sizeof(INT)))) # Int |-> ((Znth idx current (0 : Int))))
  ** (intArray.missing_i heap_pre idx (0 : Int) n_pre current)

noncomputable def pop_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre current)
|--
  “ ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (largest * sizeof(INT)))) # Int |-> ((Znth largest current (0 : Int))))
  ** (intArray.missing_i heap_pre largest (0 : Int) n_pre current)

noncomputable def pop_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre current)
|--
  “ ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (idx * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i heap_pre idx (0 : Int) n_pre current)

noncomputable def pop_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (S_before : (multiset Int)) (before : (List Int)) (current : (List Int)) (ret : Int) (idx : Int) (left : Int) (right : Int) (largest : Int) (PreH1 : ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int)))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth (0 : Int) before (0 : Int)))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre)) (PreH7 : (PrefixMaximum before n_pre ret)) (PreH8 : (multiset_maximum S_before ret)) (PreH9 : ((0 : Int) <= idx)) (PreH10 : (idx < (n_pre - 1))) (PreH11 : (left = ((idx * 2) + 1))) (PreH12 : (right = (left + 1))) (PreH13 : ((0 : Int) <= largest)) (PreH14 : (largest < (n_pre - 1))) (PreH15 : (PopSelectedChild current (n_pre - 1) idx largest)) (PreH16 : (PopLoopState before current n_pre idx)) ,
  (intArray.full heap_pre n_pre (replace_Znth (idx) ((Znth largest current (0 : Int))) (current)))
|--
  “ ((Znth idx current (0 : Int)) < (Znth largest current (0 : Int))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (ret = (Znth (0 : Int) before (0 : Int))) ” &&
  “ (ret = (multiset_max (S_before))) ” &&
  “ (heap_representation S_before before n_pre) ” &&
  “ (PrefixMaximum before n_pre ret) ” &&
  “ (multiset_maximum S_before ret) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= largest) ” &&
  “ (largest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current (n_pre - 1) idx largest) ” &&
  “ (PopLoopState before current n_pre idx) ”
  &&  (((heap_pre + (largest * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i heap_pre largest (0 : Int) n_pre (replace_Znth (idx) ((Znth largest current (0 : Int))) (current)))

noncomputable def heap_sort_safety_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (suffix : (List Int)) (active : (multiset Int)) (i : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((multiset_size (active)) = i)) (PreH7 : ((Zlength (suffix)) = (n_pre - i))) (PreH8 : (HeapSortState input active suffix)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def heap_sort_safety_wit_2 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active : (multiset Int)) (suffix : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (extracted = (multiset_max (active)))) (PreH7 : (multiset_maximum active extracted)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i))) (PreH10 : (HeapSortState input active suffix)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "extracted" ) )) # Int |-> (extracted))
  ** (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (intArray.undef_seg heap_pre (i - 1) i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def heap_sort_safety_wit_3 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active : (multiset Int)) (suffix : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (extracted = (multiset_max (active)))) (PreH7 : (multiset_maximum active extracted)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i))) (PreH10 : (HeapSortState input active suffix)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "extracted" ) )) # Int |-> (extracted))
  ** (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (intArray.undef_seg heap_pre (i - 1) i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def heap_sort_safety_wit_4 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active : (multiset Int)) (suffix : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (extracted = (multiset_max (active)))) (PreH7 : (multiset_maximum active extracted)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i))) (PreH10 : (HeapSortState input active suffix)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "extracted" ) )) # Int |-> (extracted))
  ** (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (heap_retired_cell heap_pre (i - 1) extracted)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def heap_sort_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (store_heap heap_pre (list_to_multiset (input)) n_pre)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((multiset_size ((list_to_multiset (input)))) = n_pre) ” &&
  “ (HeapSortState input (list_to_multiset (input)) (@List.nil Int)) ”
  &&  (store_heap heap_pre (list_to_multiset (input)) n_pre)
  ** (intArray.seg heap_pre n_pre n_pre (@List.nil Int))
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  TT && emp 
|--
  “ (HeapSortState input (list_to_multiset (input)) (@List.nil Int)) ” &&
  “ ((multiset_size ((list_to_multiset (input)))) = n_pre) ”
  &&  emp
)

noncomputable def heap_sort_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (HeapSortState input (list_to_multiset (input)) (@List.nil Int))

noncomputable def heap_sort_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((multiset_size ((list_to_multiset (input)))) = n_pre)

noncomputable def heap_sort_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((multiset_size ((list_to_multiset (input)))) = n_pre)) (PreH5 : (HeapSortState input (list_to_multiset (input)) (@List.nil Int))) ,
  (store_heap heap_pre (list_to_multiset (input)) n_pre)
  ** (intArray.seg heap_pre n_pre n_pre (@List.nil Int))
|--
  EX suffix : (List Int), EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((multiset_size (active)) = n_pre) ” &&
  “ ((Zlength (suffix)) = (n_pre - n_pre)) ” &&
  “ (HeapSortState input active suffix) ”
  &&  (store_heap heap_pre active n_pre)
  ** (intArray.seg heap_pre n_pre n_pre suffix)
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((multiset_size ((list_to_multiset (input)))) = n_pre)) (PreH5 : (HeapSortState input (list_to_multiset (input)) (@List.nil Int))) ,
  TT && emp 
|--
  “ ((Zlength ((@List.nil Int))) = (n_pre - n_pre)) ”
  &&  emp
)

noncomputable def heap_sort_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((multiset_size ((list_to_multiset (input)))) = n_pre)) (PreH5 : (HeapSortState input (list_to_multiset (input)) (@List.nil Int))) ,
  ((Zlength ((@List.nil Int))) = (n_pre - n_pre))

noncomputable def heap_sort_entail_wit_3 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (suffix_2 : (List Int)) (active_2 : (multiset Int)) (i : Int) (PreH1 : (i > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((multiset_size (active_2)) = i)) (PreH8 : ((Zlength (suffix_2)) = (n_pre - i))) (PreH9 : (HeapSortState input active_2 suffix_2)) ,
  (store_heap heap_pre active_2 i)
  ** (intArray.seg heap_pre i n_pre suffix_2)
|--
  EX suffix : (List Int), EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((multiset_size (active)) = i) ” &&
  “ ((Zlength (suffix)) = (n_pre - i)) ” &&
  “ (HeapSortState input active suffix) ”
  &&  (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)

noncomputable def heap_sort_entail_wit_4 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active_2 : (multiset Int)) (suffix_2 : (List Int)) (i : Int) (retval : Int) (PreH1 : (retval = (multiset_max (active_2)))) (PreH2 : (multiset_maximum active_2 retval)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((multiset_size (active_2)) = i)) (PreH9 : ((Zlength (suffix_2)) = (n_pre - i))) (PreH10 : (HeapSortState input active_2 suffix_2)) ,
  (store_heap heap_pre (multiset_remove (active_2) ((multiset_max (active_2)))) (i - 1))
  ** (intArray.undef_seg heap_pre (i - 1) i)
  ** (intArray.seg heap_pre i n_pre suffix_2)
|--
  EX suffix : (List Int), EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (retval = (multiset_max (active))) ” &&
  “ (multiset_maximum active retval) ” &&
  “ ((multiset_size (active)) = i) ” &&
  “ ((Zlength (suffix)) = (n_pre - i)) ” &&
  “ (HeapSortState input active suffix) ”
  &&  (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (intArray.undef_seg heap_pre (i - 1) i)
  ** (intArray.seg heap_pre i n_pre suffix)

noncomputable def heap_sort_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active_2 : (multiset Int)) (suffix_2 : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (extracted = (multiset_max (active_2)))) (PreH7 : (multiset_maximum active_2 extracted)) (PreH8 : ((multiset_size (active_2)) = i)) (PreH9 : ((Zlength (suffix_2)) = (n_pre - i))) (PreH10 : (HeapSortState input active_2 suffix_2)) ,
  (((heap_pre + ((i - 1) * sizeof(INT)))) # Int |-> (extracted))
  ** (store_heap heap_pre (multiset_remove (active_2) ((multiset_max (active_2)))) (i - 1))
  ** (intArray.seg heap_pre i n_pre suffix_2)
|--
  EX suffix : (List Int), EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (extracted = (multiset_max (active))) ” &&
  “ (multiset_maximum active extracted) ” &&
  “ ((multiset_size (active)) = i) ” &&
  “ ((Zlength (suffix)) = (n_pre - i)) ” &&
  “ (HeapSortState input active suffix) ”
  &&  (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (heap_retired_cell heap_pre (i - 1) extracted)
  ** (intArray.seg heap_pre i n_pre suffix)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active_2 : (multiset Int)) (suffix_2 : (List Int)) (i : Int) (extracted : Int) (PreH1 : (extracted <= INT_MAX)) (PreH2 : (extracted >= INT_MIN)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (extracted = (multiset_max (active_2)))) (PreH9 : (multiset_maximum active_2 extracted)) (PreH10 : ((multiset_size (active_2)) = i)) (PreH11 : ((Zlength (suffix_2)) = (n_pre - i))) (PreH12 : (HeapSortState input active_2 suffix_2)) ,
  (((heap_pre + ((i - 1) * sizeof(INT)))) # Int |-> (extracted))
  ** (store_heap heap_pre (multiset_remove (active_2) ((multiset_max (active_2)))) (i - 1))
|--
  EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (extracted = (multiset_max (active))) ” &&
  “ (multiset_maximum active extracted) ” &&
  “ ((multiset_size (active)) = i) ” &&
  “ ((Zlength (suffix_2)) = (n_pre - i)) ” &&
  “ (HeapSortState input active suffix_2) ”
  &&  (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (heap_retired_cell heap_pre (i - 1) extracted)
)

noncomputable def heap_sort_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active_2 : (multiset Int)) (suffix_2 : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (extracted = (multiset_max (active_2)))) (PreH7 : (multiset_maximum active_2 extracted)) (PreH8 : ((multiset_size (active_2)) = i)) (PreH9 : ((Zlength (suffix_2)) = (n_pre - i))) (PreH10 : (HeapSortState input active_2 suffix_2)) ,
  (store_heap heap_pre (multiset_remove (active_2) ((multiset_max (active_2)))) (i - 1))
  ** (heap_retired_cell heap_pre (i - 1) extracted)
  ** (intArray.seg heap_pre i n_pre suffix_2)
|--
  EX suffix : (List Int), EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((multiset_size ((multiset_remove (active) ((multiset_max (active)))))) = (i - 1)) ” &&
  “ ((Zlength ((extracted :: suffix))) = (n_pre - (i - 1))) ” &&
  “ (HeapSortState input (multiset_remove (active) ((multiset_max (active)))) (extracted :: suffix)) ”
  &&  (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (intArray.seg heap_pre (i - 1) n_pre (extracted :: suffix))
) \/
(
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active_2 : (multiset Int)) (suffix_2 : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (extracted = (multiset_max (active_2)))) (PreH7 : (multiset_maximum active_2 extracted)) (PreH8 : ((multiset_size (active_2)) = i)) (PreH9 : ((Zlength (suffix_2)) = (n_pre - i))) (PreH10 : (HeapSortState input active_2 suffix_2)) ,
  (store_heap heap_pre (multiset_remove (active_2) ((multiset_max (active_2)))) (i - 1))
  ** (heap_retired_cell heap_pre (i - 1) extracted)
  ** (intArray.seg heap_pre i n_pre suffix_2)
|--
  EX suffix : (List Int), EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((multiset_size ((multiset_remove (active) ((multiset_max (active)))))) = (i - 1)) ” &&
  “ ((Zlength ((extracted :: suffix))) = (n_pre - (i - 1))) ” &&
  “ (HeapSortState input (multiset_remove (active) ((multiset_max (active)))) (extracted :: suffix)) ”
  &&  (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (intArray.seg heap_pre (i - 1) n_pre (extracted :: suffix))
)

noncomputable def heap_sort_entail_wit_7 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active_2 : (multiset Int)) (suffix_2 : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((multiset_size ((multiset_remove (active_2) ((multiset_max (active_2)))))) = i)) (PreH7 : ((Zlength ((extracted :: suffix_2))) = (n_pre - i))) (PreH8 : (HeapSortState input (multiset_remove (active_2) ((multiset_max (active_2)))) (extracted :: suffix_2))) ,
  (store_heap heap_pre (multiset_remove (active_2) ((multiset_max (active_2)))) i)
  ** (intArray.seg heap_pre i n_pre (extracted :: suffix_2))
|--
  EX suffix : (List Int), EX active : (multiset Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((multiset_size (active)) = i) ” &&
  “ ((Zlength (suffix)) = (n_pre - i)) ” &&
  “ (HeapSortState input active suffix) ”
  &&  (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)

noncomputable def heap_sort_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (suffix : (List Int)) (active : (multiset Int)) (i : Int) (PreH1 : (i <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((multiset_size (active)) = i)) (PreH8 : ((Zlength (suffix)) = (n_pre - i))) (PreH9 : (HeapSortState input active suffix)) ,
  (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  EX output : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (i = (0 : Int)) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output)) = n_pre) ” &&
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full heap_pre n_pre output)
) \/
(
forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (suffix : (List Int)) (active : (multiset Int)) (i : Int) (PreH1 : (i <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((multiset_size (active)) = i)) (PreH8 : ((Zlength (suffix)) = (n_pre - i))) (PreH9 : (HeapSortState input active suffix)) ,
  (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  EX output : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (i = (0 : Int)) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output)) = n_pre) ” &&
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full heap_pre n_pre output)
)

noncomputable def heap_sort_return_wit_1 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (output_2 : (List Int)) (i : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_2)) = n_pre)) (PreH6 : (Permutation input output_2)) (PreH7 : (increasing output_2)) ,
  (intArray.full heap_pre n_pre output_2)
|--
  EX output : (List Int),
  “ ((Zlength (output)) = n_pre) ” &&
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full heap_pre n_pre output)

noncomputable def heap_sort_partial_solve_wit_1_pure : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full heap_pre n_pre input)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ”

noncomputable def heap_sort_partial_solve_wit_1_aux : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (intArray.full heap_pre n_pre input)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ”
  &&  (intArray.full heap_pre n_pre input)

noncomputable def heap_sort_partial_solve_wit_1 : Prop := heap_sort_partial_solve_wit_1_pure -> heap_sort_partial_solve_wit_1_aux

noncomputable def heap_sort_partial_solve_wit_2_pure : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active : (multiset Int)) (suffix : (List Int)) (i : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((multiset_size (active)) = i)) (PreH7 : ((Zlength (suffix)) = (n_pre - i))) (PreH8 : (HeapSortState input active suffix)) ,
  ((( &( "extracted" ) )) # Int |->_)
  ** ((( &( "heap" ) )) # Ptr |-> (heap_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  “ (1 <= i) ”

noncomputable def heap_sort_partial_solve_wit_2_aux : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active : (multiset Int)) (suffix : (List Int)) (i : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((multiset_size (active)) = i)) (PreH7 : ((Zlength (suffix)) = (n_pre - i))) (PreH8 : (HeapSortState input active suffix)) ,
  (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  “ (1 <= i) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((multiset_size (active)) = i) ” &&
  “ ((Zlength (suffix)) = (n_pre - i)) ” &&
  “ (HeapSortState input active suffix) ”
  &&  (store_heap heap_pre active i)
  ** (intArray.seg heap_pre i n_pre suffix)

noncomputable def heap_sort_partial_solve_wit_2 : Prop := heap_sort_partial_solve_wit_2_pure -> heap_sort_partial_solve_wit_2_aux

noncomputable def heap_sort_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (heap_pre : Int) (input : (List Int)) (active : (multiset Int)) (suffix : (List Int)) (i : Int) (extracted : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (extracted = (multiset_max (active)))) (PreH7 : (multiset_maximum active extracted)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i))) (PreH10 : (HeapSortState input active suffix)) ,
  (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (intArray.undef_seg heap_pre (i - 1) i)
  ** (intArray.seg heap_pre i n_pre suffix)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (extracted = (multiset_max (active))) ” &&
  “ (multiset_maximum active extracted) ” &&
  “ ((multiset_size (active)) = i) ” &&
  “ ((Zlength (suffix)) = (n_pre - i)) ” &&
  “ (HeapSortState input active suffix) ”
  &&  (((heap_pre + ((i - 1) * sizeof(INT)))) # Int |->_)
  ** (store_heap heap_pre (multiset_remove (active) ((multiset_max (active)))) (i - 1))
  ** (intArray.seg heap_pre i n_pre suffix)


structure VC_Correct : Type where
  proof_of_push_safety_wit_1 : push_safety_wit_1
  proof_of_push_safety_wit_2 : push_safety_wit_2
  proof_of_push_safety_wit_3 : push_safety_wit_3
  proof_of_push_safety_wit_4 : push_safety_wit_4
  proof_of_push_safety_wit_5 : push_safety_wit_5
  proof_of_push_entail_wit_8_2 : push_entail_wit_8_2
  proof_of_push_return_wit_1 : push_return_wit_1
  proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1
  proof_of_push_partial_solve_wit_2 : push_partial_solve_wit_2
  proof_of_push_partial_solve_wit_3 : push_partial_solve_wit_3
  proof_of_push_partial_solve_wit_4 : push_partial_solve_wit_4
  proof_of_push_partial_solve_wit_5 : push_partial_solve_wit_5
  proof_of_push_partial_solve_wit_6 : push_partial_solve_wit_6
  proof_of_push_partial_solve_wit_7 : push_partial_solve_wit_7
  proof_of_build_safety_wit_1 : build_safety_wit_1
  proof_of_build_safety_wit_2 : build_safety_wit_2
  proof_of_build_safety_wit_3 : build_safety_wit_3
  proof_of_build_entail_wit_3 : build_entail_wit_3
  proof_of_build_entail_wit_5 : build_entail_wit_5
  proof_of_build_return_wit_1 : build_return_wit_1
  proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1
  proof_of_build_partial_solve_wit_2_pure : build_partial_solve_wit_2_pure
  proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2
  proof_of_pop_safety_wit_1 : pop_safety_wit_1
  proof_of_pop_safety_wit_2 : pop_safety_wit_2
  proof_of_pop_safety_wit_3 : pop_safety_wit_3
  proof_of_pop_safety_wit_4 : pop_safety_wit_4
  proof_of_pop_safety_wit_5 : pop_safety_wit_5
  proof_of_pop_safety_wit_6 : pop_safety_wit_6
  proof_of_pop_safety_wit_7 : pop_safety_wit_7
  proof_of_pop_safety_wit_8 : pop_safety_wit_8
  proof_of_pop_safety_wit_9 : pop_safety_wit_9
  proof_of_pop_safety_wit_10 : pop_safety_wit_10
  proof_of_pop_safety_wit_11 : pop_safety_wit_11
  proof_of_pop_safety_wit_12 : pop_safety_wit_12
  proof_of_pop_safety_wit_13 : pop_safety_wit_13
  proof_of_pop_safety_wit_14 : pop_safety_wit_14
  proof_of_pop_safety_wit_15 : pop_safety_wit_15
  proof_of_pop_safety_wit_16 : pop_safety_wit_16
  proof_of_pop_safety_wit_17 : pop_safety_wit_17
  proof_of_pop_safety_wit_18 : pop_safety_wit_18
  proof_of_pop_safety_wit_19 : pop_safety_wit_19
  proof_of_pop_safety_wit_20 : pop_safety_wit_20
  proof_of_pop_entail_wit_2 : pop_entail_wit_2
  proof_of_pop_return_wit_1 : pop_return_wit_1
  proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1
  proof_of_pop_partial_solve_wit_2 : pop_partial_solve_wit_2
  proof_of_pop_partial_solve_wit_3 : pop_partial_solve_wit_3
  proof_of_pop_partial_solve_wit_4 : pop_partial_solve_wit_4
  proof_of_pop_partial_solve_wit_5 : pop_partial_solve_wit_5
  proof_of_pop_partial_solve_wit_6 : pop_partial_solve_wit_6
  proof_of_pop_partial_solve_wit_7 : pop_partial_solve_wit_7
  proof_of_pop_partial_solve_wit_8 : pop_partial_solve_wit_8
  proof_of_pop_partial_solve_wit_9 : pop_partial_solve_wit_9
  proof_of_pop_partial_solve_wit_10 : pop_partial_solve_wit_10
  proof_of_pop_partial_solve_wit_11 : pop_partial_solve_wit_11
  proof_of_heap_sort_safety_wit_1 : heap_sort_safety_wit_1
  proof_of_heap_sort_safety_wit_2 : heap_sort_safety_wit_2
  proof_of_heap_sort_safety_wit_3 : heap_sort_safety_wit_3
  proof_of_heap_sort_safety_wit_4 : heap_sort_safety_wit_4
  proof_of_heap_sort_entail_wit_3 : heap_sort_entail_wit_3
  proof_of_heap_sort_entail_wit_4 : heap_sort_entail_wit_4
  proof_of_heap_sort_entail_wit_7 : heap_sort_entail_wit_7
  proof_of_heap_sort_return_wit_1 : heap_sort_return_wit_1
  proof_of_heap_sort_partial_solve_wit_1_pure : heap_sort_partial_solve_wit_1_pure
  proof_of_heap_sort_partial_solve_wit_1 : heap_sort_partial_solve_wit_1
  proof_of_heap_sort_partial_solve_wit_2_pure : heap_sort_partial_solve_wit_2_pure
  proof_of_heap_sort_partial_solve_wit_2 : heap_sort_partial_solve_wit_2
  proof_of_heap_sort_partial_solve_wit_3 : heap_sort_partial_solve_wit_3
  proof_of_push_entail_wit_1 : push_entail_wit_1
  proof_of_push_entail_wit_2 : push_entail_wit_2
  proof_of_push_entail_wit_3 : push_entail_wit_3
  proof_of_push_entail_wit_4 : push_entail_wit_4
  proof_of_push_entail_wit_5 : push_entail_wit_5
  proof_of_push_entail_wit_6 : push_entail_wit_6
  proof_of_push_entail_wit_7 : push_entail_wit_7
  proof_of_push_entail_wit_8_1 : push_entail_wit_8_1
  proof_of_push_entail_wit_9 : push_entail_wit_9
  proof_of_build_entail_wit_1 : build_entail_wit_1
  proof_of_build_entail_wit_2 : build_entail_wit_2
  proof_of_build_entail_wit_4 : build_entail_wit_4
  proof_of_build_entail_wit_6_1 : build_entail_wit_6_1
  proof_of_build_entail_wit_6_2 : build_entail_wit_6_2
  proof_of_pop_entail_wit_1 : pop_entail_wit_1
  proof_of_pop_entail_wit_3 : pop_entail_wit_3
  proof_of_pop_entail_wit_4 : pop_entail_wit_4
  proof_of_pop_entail_wit_5 : pop_entail_wit_5
  proof_of_pop_entail_wit_6 : pop_entail_wit_6
  proof_of_pop_entail_wit_7_1 : pop_entail_wit_7_1
  proof_of_pop_entail_wit_7_2 : pop_entail_wit_7_2
  proof_of_pop_entail_wit_7_3 : pop_entail_wit_7_3
  proof_of_pop_entail_wit_8 : pop_entail_wit_8
  proof_of_pop_entail_wit_9 : pop_entail_wit_9
  proof_of_pop_entail_wit_10 : pop_entail_wit_10
  proof_of_pop_entail_wit_11_1 : pop_entail_wit_11_1
  proof_of_pop_entail_wit_11_2 : pop_entail_wit_11_2
  proof_of_pop_entail_wit_12 : pop_entail_wit_12
  proof_of_pop_entail_wit_13 : pop_entail_wit_13
  proof_of_pop_return_wit_2 : pop_return_wit_2
  proof_of_heap_sort_entail_wit_1 : heap_sort_entail_wit_1
  proof_of_heap_sort_entail_wit_2 : heap_sort_entail_wit_2
  proof_of_heap_sort_entail_wit_5 : heap_sort_entail_wit_5
  proof_of_heap_sort_entail_wit_6 : heap_sort_entail_wit_6
  proof_of_heap_sort_entail_wit_8 : heap_sort_entail_wit_8

end SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_goal
