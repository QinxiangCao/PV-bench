import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Data_structures.stack.stack_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Data_structures.stack.stack_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance stack_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def push_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (stack_pre : Int) (before : sll) (PreH1 : (n_pre < stack_capacity)) ,
  (store_stack stack_pre before n_pre)
  ** (intArray.undef_seg stack_pre n_pre (n_pre + 1))
|--
  EX concrete : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < stack_capacity) ” &&
  “ (StackConcreteView before concrete n_pre) ”
  &&  (intArray.full stack_pre n_pre concrete)
  ** (intArray.undef_seg stack_pre n_pre (n_pre + 1))
) \/
(
forall (n_pre : Int) (stack_pre : Int) (before : sll) (PreH1 : (n_pre < stack_capacity)) ,
  (store_stack stack_pre before n_pre)
|--
  EX concrete : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < stack_capacity) ” &&
  “ (StackConcreteView before concrete n_pre) ”
  &&  (intArray.full stack_pre n_pre concrete)
)

noncomputable def push_entail_wit_2 : Prop :=
  (
forall (x_pre : Int) (n_pre : Int) (stack_pre : Int) (before : sll) (concrete : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < stack_capacity)) (PreH3 : (StackConcreteView before concrete n_pre)) ,
  (intArray.full stack_pre (n_pre + 1) (concrete ++ (x_pre :: (@List.nil Int))))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < stack_capacity) ”
  &&  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1))
) \/
(
forall (x_pre : Int) (n_pre : Int) (stack_pre : Int) (before : sll) (concrete : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < stack_capacity)) (PreH3 : (StackConcreteView before concrete n_pre)) ,
  (intArray.full stack_pre (n_pre + 1) (concrete ++ (x_pre :: (@List.nil Int))))
|--
  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1))
)

noncomputable def push_entail_wit_2_split_goal_spatial : Prop :=
  forall (x_pre : Int) (n_pre : Int) (stack_pre : Int) (before : sll) (concrete : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < stack_capacity)) (PreH3 : (StackConcreteView before concrete n_pre)) ,
  (intArray.full stack_pre (n_pre + 1) (concrete ++ (x_pre :: (@List.nil Int))))
|--
  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1))

noncomputable def push_return_wit_1 : Prop :=
  forall (x_pre : Int) (n_pre : Int) (stack_pre : Int) (before : sll) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < stack_capacity)) ,
  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1))
|--
  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1))

noncomputable def push_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (before : sll) (concrete : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < stack_capacity)) (PreH3 : (StackConcreteView before concrete n_pre)) ,
  (intArray.full stack_pre n_pre concrete)
  ** (intArray.undef_seg stack_pre n_pre (n_pre + 1))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < stack_capacity) ” &&
  “ (StackConcreteView before concrete n_pre) ”
  &&  (((stack_pre + (n_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.full stack_pre n_pre concrete)

noncomputable def pop_safety_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (concrete : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (StackConcreteView (sll_cons (top) (rest)) concrete n_pre)) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "stack" ) )) # Ptr |-> (stack_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full stack_pre n_pre concrete)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_2 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (concrete : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (StackConcreteView (sll_cons (top) (rest)) concrete n_pre)) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "stack" ) )) # Ptr |-> (stack_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full stack_pre n_pre concrete)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (PreH1 : (1 <= n_pre)) ,
  (store_stack stack_pre (sll_cons (top) (rest)) n_pre)
|--
  EX concrete : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (StackConcreteView (sll_cons (top) (rest)) concrete n_pre) ”
  &&  (intArray.full stack_pre n_pre concrete)
) \/
(
forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (PreH1 : (1 <= n_pre)) ,
  (store_stack stack_pre (sll_cons (top) (rest)) n_pre)
|--
  EX concrete : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (StackConcreteView (sll_cons (top) (rest)) concrete n_pre) ”
  &&  (intArray.full stack_pre n_pre concrete)
)

noncomputable def pop_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (concrete : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (StackConcreteView (sll_cons (top) (rest)) concrete n_pre)) ,
  (intArray.full stack_pre n_pre concrete)
  ** ((( &( "ret" ) )) # Int |-> ((Znth (n_pre - 1) concrete (0 : Int))))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ”
  &&  ((( &( "ret" ) )) # Int |-> (top))
  ** (store_stack stack_pre rest (n_pre - 1))
  ** (intArray.undef_seg stack_pre (n_pre - 1) n_pre)
) \/
(
forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (concrete : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (StackConcreteView (sll_cons (top) (rest)) concrete n_pre)) ,
  (intArray.full stack_pre n_pre concrete)
|--
  “ ((Znth (n_pre - 1) concrete (0 : Int)) = top) ”
  &&  (store_stack stack_pre rest (n_pre - 1))
  ** (intArray.undef_seg stack_pre (n_pre - 1) n_pre)
)

noncomputable def pop_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (concrete : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (StackConcreteView (sll_cons (top) (rest)) concrete n_pre)) ,
  (intArray.full stack_pre n_pre concrete)
|--
  “ ((Znth (n_pre - 1) concrete (0 : Int)) = top) ”

noncomputable def pop_entail_wit_2_split_goal_spatial : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (concrete : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (StackConcreteView (sll_cons (top) (rest)) concrete n_pre)) ,
  (intArray.full stack_pre n_pre concrete)
|--
  (store_stack stack_pre rest (n_pre - 1))
  ** (intArray.undef_seg stack_pre (n_pre - 1) n_pre)

noncomputable def pop_return_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) ,
  (store_stack stack_pre rest (n_pre - 1))
  ** (intArray.undef_seg stack_pre (n_pre - 1) n_pre)
|--
  “ (top = top) ”
  &&  (store_stack stack_pre rest (n_pre - 1))
  ** (intArray.undef_seg stack_pre (n_pre - 1) n_pre)

noncomputable def pop_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (rest : sll) (top : Int) (concrete : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (StackConcreteView (sll_cons (top) (rest)) concrete n_pre)) ,
  (intArray.full stack_pre n_pre concrete)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (StackConcreteView (sll_cons (top) (rest)) concrete n_pre) ”
  &&  (((stack_pre + ((n_pre - 1) * sizeof(INT)))) # Int |-> ((Znth (n_pre - 1) concrete (0 : Int))))
  ** (intArray.missing_i stack_pre (n_pre - 1) (0 : Int) n_pre concrete)

noncomputable def build_safety_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stack" ) )) # Ptr |-> (stack_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full stack_pre n_pre input)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_2 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  ((( &( "stack" ) )) # Ptr |-> (stack_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full stack_pre n_pre input)
|--
  “ False ”

noncomputable def build_safety_wit_3 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (next : sll) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix next input (i + 1))) ,
  ((( &( "stack" ) )) # Ptr |-> (stack_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (store_stack stack_pre next (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_entail_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (intArray.full stack_pre n_pre input)
|--
  (“ (n_pre = (0 : Int)) ” &&
  “ (1 = 1) ” &&
  “ ((Zlength (input)) = n_pre) ”
  &&  (intArray.full stack_pre n_pre input))
  ||
  (EX «prefix» : sll,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildStackPrefix «prefix» input 1) ”
  &&  (store_stack stack_pre «prefix» 1)
  ** (intArray.seg stack_pre 1 n_pre (sublist (1) (n_pre) (input))))

noncomputable def build_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (prefix_2 : sll) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix_2 input i)) ,
  (intArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)))
  ** (store_stack stack_pre prefix_2 i)
|--
  EX «prefix» : sll,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth (i - i) (sublist (i) (n_pre) (input)) (0 : Int)) = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildStackPrefix «prefix» input i) ”
  &&  (store_stack stack_pre «prefix» i)
  ** (intArray.undef_seg stack_pre i (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
) \/
(
forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (prefix_2 : sll) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix_2 input i)) ,
  (intArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)))
  ** (store_stack stack_pre prefix_2 i)
|--
  EX «prefix» : sll,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth (i - i) (sublist (i) (n_pre) (input)) (0 : Int)) = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildStackPrefix «prefix» input i) ”
  &&  (store_stack stack_pre «prefix» i)
  ** (intArray.undef_seg stack_pre i (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
)

noncomputable def build_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  (store_stack stack_pre (sll_cons (x) («prefix»)) (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  EX next : sll,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildStackPrefix next input (i + 1)) ”
  &&  (store_stack stack_pre next (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
) \/
(
forall (n_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  TT && emp 
|--
  “ (BuildStackPrefix (sll_cons (x) («prefix»)) input (i + 1)) ”
  &&  emp
)

noncomputable def build_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  (BuildStackPrefix (sll_cons (x) («prefix»)) input (i + 1))

noncomputable def build_entail_wit_4 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (next : sll) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix next input (i + 1))) ,
  (store_stack stack_pre next (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  EX «prefix» : sll,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildStackPrefix «prefix» input (i + 1)) ”
  &&  (store_stack stack_pre «prefix» (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))

noncomputable def build_entail_wit_5_1 : Prop :=
  (
forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (intArray.full stack_pre n_pre input)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ”
  &&  (store_stack stack_pre (sll_from_array (input)) n_pre)
) \/
(
forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (intArray.full stack_pre n_pre input)
|--
  “ ((0 : Int) <= stack_capacity) ”
  &&  (store_stack stack_pre (sll_from_array (input)) n_pre)
)

noncomputable def build_entail_wit_5_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (intArray.full stack_pre n_pre input)
|--
  “ ((0 : Int) <= stack_capacity) ”

noncomputable def build_entail_wit_5_1_split_goal_spatial : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (intArray.full stack_pre n_pre input)
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre)

noncomputable def build_entail_wit_5_2 : Prop :=
  (
forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  (store_stack stack_pre «prefix» i)
  ** (intArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ ((Zlength (input)) = n_pre) ”
  &&  (store_stack stack_pre (sll_from_array (input)) n_pre)
) \/
(
forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  (store_stack stack_pre «prefix» i)
  ** (intArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre)
)

noncomputable def build_entail_wit_5_2_split_goal_spatial : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  (store_stack stack_pre «prefix» i)
  ** (intArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre)

noncomputable def build_return_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (store_stack stack_pre (sll_from_array (input)) n_pre)
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre)

noncomputable def build_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  (store_stack stack_pre «prefix» i)
  ** (intArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)))
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildStackPrefix «prefix» input i) ”
  &&  (((stack_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - i) (sublist (i) (n_pre) (input)) (0 : Int))))
  ** (intArray.missing_i stack_pre i i n_pre (sublist (i) (n_pre) (input)))
  ** (store_stack stack_pre «prefix» i)

noncomputable def build_partial_solve_wit_2_pure : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  ((( &( "stack" ) )) # Ptr |-> (stack_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (store_stack stack_pre «prefix» i)
  ** (intArray.undef_seg stack_pre i (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  “ (i < stack_capacity) ”

noncomputable def build_partial_solve_wit_2_aux : Prop :=
  forall (n_pre : Int) (stack_pre : Int) (input : (List Int)) («prefix» : sll) (i : Int) (x : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input (0 : Int)))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix «prefix» input i)) ,
  (store_stack stack_pre «prefix» i)
  ** (intArray.undef_seg stack_pre i (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))
|--
  “ (i < stack_capacity) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= stack_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i input (0 : Int))) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (BuildStackPrefix «prefix» input i) ”
  &&  (store_stack stack_pre «prefix» i)
  ** (intArray.undef_seg stack_pre i (i + 1))
  ** (intArray.seg stack_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (input)))

noncomputable def build_partial_solve_wit_2 : Prop := build_partial_solve_wit_2_pure -> build_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_push_return_wit_1 : push_return_wit_1
  proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1
  proof_of_pop_safety_wit_1 : pop_safety_wit_1
  proof_of_pop_safety_wit_2 : pop_safety_wit_2
  proof_of_pop_return_wit_1 : pop_return_wit_1
  proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1
  proof_of_build_safety_wit_1 : build_safety_wit_1
  proof_of_build_safety_wit_2 : build_safety_wit_2
  proof_of_build_safety_wit_3 : build_safety_wit_3
  proof_of_build_entail_wit_4 : build_entail_wit_4
  proof_of_build_return_wit_1 : build_return_wit_1
  proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1
  proof_of_build_partial_solve_wit_2_pure : build_partial_solve_wit_2_pure
  proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2
  proof_of_push_entail_wit_1 : push_entail_wit_1
  proof_of_push_entail_wit_2 : push_entail_wit_2
  proof_of_pop_entail_wit_1 : pop_entail_wit_1
  proof_of_pop_entail_wit_2 : pop_entail_wit_2
  proof_of_build_entail_wit_1 : build_entail_wit_1
  proof_of_build_entail_wit_2 : build_entail_wit_2
  proof_of_build_entail_wit_3 : build_entail_wit_3
  proof_of_build_entail_wit_5_1 : build_entail_wit_5_1
  proof_of_build_entail_wit_5_2 : build_entail_wit_5_2

end SimpleC.EE.LLM_bench.Data_structures.stack.stack_goal
