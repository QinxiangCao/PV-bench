import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal

/-
These twelve source verification conditions preserve the stored Coq goals before
symexec substitutes values using explicit equality premises. Each equivalence
below applies those premises inside the quantified context.
Source: Rocq/examples/LLM_bench/Data_structures/priority_queue_decrease_key/priority_queue_decrease_key_goal.v
Source SHA-256: 750fa7b5611f22135d9fea3a22a41a86160754382947f910db468abf09221d2c
-/
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_vc_compat
open AUXLib SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib
open SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
namespace SourceVC

-- Coq source line 284; retained premise: PreH11.
noncomputable def pqdk_sift_up_entail_wit_4 : Prop :=
(
forall (n_pre: Int) (data_bound_pre: Int) (pos_pre: Int) (data_pre: Int) (key_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (child: Int) (parent: Int) (tmp_key: Int) (tmp_data: Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 (0 : Int)) > (Znth child key_values_2 (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values_2 (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values_2 (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values_2 (0 : Int)))) (PreH13 : ((Znth parent data_values_2 (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values_2 (0 : Int)))) (PreH15 : ((Znth child data_values_2 (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (intArray.full data_pre n_pre (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) )
  **  (intArray.full key_pre n_pre (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 (0 : Int))) (key_values_2)))) )
  **  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values_2 (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values_2 (0 : Int))) (child) (pos_values_2)))) )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.undef_seg data_pre n_pre capacity )
|--
  EX pos_values : (List Int), EX data_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ ((0 : Int) < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ ((0 : Int) <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (tmp_key = (Znth child key_values (0 : Int))) ” 
  &&  “ (tmp_data = (Znth child data_values (0 : Int))) ” 
  &&  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” 
  &&  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” 
  &&  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre parent ) ”
  &&  (intArray.full key_pre n_pre key_values )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (child: Int) (parent: Int) (tmp_key: Int) (tmp_data: Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 (0 : Int)) > (Znth child key_values_2 (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values_2 (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values_2 (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values_2 (0 : Int)))) (PreH13 : ((Znth parent data_values_2 (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values_2 (0 : Int)))) (PreH15 : ((Znth child data_values_2 (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  TT && emp 
|--
  “ (SiftUpState M (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth child data_values_2 (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values_2 (0 : Int))) (child) (pos_values_2)))) data_bound_pre n_pre parent ) ” 
  &&  “ ((Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (0 : Int))) ” 
  &&  “ ((Znth parent (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth parent (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (0 : Int))) ” 
  &&  “ (tmp_data = (Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (0 : Int))) ” 
  &&  “ (tmp_key = (Znth child (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 (0 : Int))) (key_values_2)))) (0 : Int))) ”
  &&  emp
)

-- Coq source line 329; retained premise: PreH11.
noncomputable def pqdk_sift_up_entail_wit_4_split_goal_1 : Prop :=
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (child: Int) (parent: Int) (tmp_key: Int) (tmp_data: Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 (0 : Int)) > (Znth child key_values_2 (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values_2 (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values_2 (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values_2 (0 : Int)))) (PreH13 : ((Znth parent data_values_2 (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values_2 (0 : Int)))) (PreH15 : ((Znth child data_values_2 (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (SiftUpState M (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth child data_values_2 (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values_2 (0 : Int))) (child) (pos_values_2)))) data_bound_pre n_pre parent )

-- Coq source line 1244; retained premise: PreH8.
noncomputable def pqdk_sift_down_entail_wit_3_1 : Prop :=
(
forall (n_pre: Int) (data_bound_pre: Int) (pos_pre: Int) (data_pre: Int) (key_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) < (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH8 : (right = (left + (1 : Int) ))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (intArray.full key_pre n_pre key_values_2 )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values_2 )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX data_values : (List Int), EX pos_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ ((0 : Int) <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * (2 : Int) ) + (1 : Int) )) ” 
  &&  “ (right = (left + (1 : Int) )) ” 
  &&  “ ((0 : Int) <= right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current right ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (intArray.full key_pre n_pre key_values )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) < (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH8 : (right = (left + (1 : Int) ))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current right ) ”
  &&  emp
)

-- Coq source line 1278; retained premise: PreH8.
noncomputable def pqdk_sift_down_entail_wit_3_1_split_goal_1 : Prop :=
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) < (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH8 : (right = (left + (1 : Int) ))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SelectedChild key_values_2 n_pre current right )

-- Coq source line 1283; retained premise: PreH8.
noncomputable def pqdk_sift_down_entail_wit_3_2 : Prop :=
(
forall (n_pre: Int) (data_bound_pre: Int) (pos_pre: Int) (data_pre: Int) (key_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH7 : (right = (left + (1 : Int) ))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (intArray.full key_pre n_pre key_values_2 )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values_2 )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX data_values : (List Int), EX pos_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ ((0 : Int) <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * (2 : Int) ) + (1 : Int) )) ” 
  &&  “ (right = (left + (1 : Int) )) ” 
  &&  “ ((0 : Int) <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (intArray.full key_pre n_pre key_values )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH7 : (right = (left + (1 : Int) ))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current smallest ) ”
  &&  emp
)

-- Coq source line 1317; retained premise: PreH8.
noncomputable def pqdk_sift_down_entail_wit_3_2_split_goal_1 : Prop :=
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH7 : (right = (left + (1 : Int) ))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SelectedChild key_values_2 n_pre current smallest )

-- Coq source line 1322; retained premise: PreH9.
noncomputable def pqdk_sift_down_entail_wit_3_3 : Prop :=
(
forall (n_pre: Int) (data_bound_pre: Int) (pos_pre: Int) (data_pre: Int) (key_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) >= (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH8 : (right = (left + (1 : Int) ))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (intArray.full key_pre n_pre key_values_2 )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values_2 )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX data_values : (List Int), EX pos_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ ((0 : Int) <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * (2 : Int) ) + (1 : Int) )) ” 
  &&  “ (right = (left + (1 : Int) )) ” 
  &&  “ ((0 : Int) <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (intArray.full key_pre n_pre key_values )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) >= (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH8 : (right = (left + (1 : Int) ))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current smallest ) ”
  &&  emp
)

-- Coq source line 1356; retained premise: PreH9.
noncomputable def pqdk_sift_down_entail_wit_3_3_split_goal_1 : Prop :=
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) >= (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH8 : (right = (left + (1 : Int) ))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SelectedChild key_values_2 n_pre current smallest )

-- Coq source line 1361; retained premise: PreH6.
noncomputable def pqdk_sift_down_entail_wit_4 : Prop :=
(
forall (n_pre: Int) (data_bound_pre: Int) (pos_pre: Int) (data_pre: Int) (key_pre: Int) (capacity: Int) (M: partial_map) (key_values: (List Int)) (data_values: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH7 : (right = (left + (1 : Int) ))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  (intArray.full data_pre n_pre data_values )
  **  (intArray.full key_pre n_pre key_values )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX pos_values : (List Int), EX data_values_2 : (List Int), EX key_values_2 : (List Int),
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ ((0 : Int) <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * (2 : Int) ) + (1 : Int) )) ” 
  &&  “ (right = (left + (1 : Int) )) ” 
  &&  “ ((0 : Int) <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ ((0 : Int) <= right) ” 
  &&  “ ((0 : Int) <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int))) ” 
  &&  “ ((Znth current key_values (0 : Int)) = (Znth current key_values_2 (0 : Int))) ” 
  &&  “ ((Znth current data_values (0 : Int)) = (Znth current data_values_2 (0 : Int))) ” 
  &&  “ ((0 : Int) <= (Znth current data_values_2 (0 : Int))) ” 
  &&  “ ((Znth current data_values_2 (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth smallest data_values_2 (0 : Int))) ” 
  &&  “ ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values_2 n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values_2 data_values_2 pos_values data_bound_pre n_pre current ) ”
  &&  (intArray.full key_pre n_pre key_values_2 )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values_2 )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values: (List Int)) (data_values: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH7 : (right = (left + (1 : Int) ))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” 
  &&  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” 
  &&  “ (current < smallest) ” 
  &&  “ (left < n_pre) ”
  &&  emp
)

-- Coq source line 1436; retained premise: PreH6.
noncomputable def pqdk_sift_down_entail_wit_4_split_goal_6 : Prop :=
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values: (List Int)) (data_values: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH7 : (right = (left + (1 : Int) ))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  (left < n_pre)

-- Coq source line 1441; retained premise: PreH15.
noncomputable def pqdk_sift_down_entail_wit_5 : Prop :=
(
forall (n_pre: Int) (data_bound_pre: Int) (pos_pre: Int) (data_pre: Int) (key_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (tmp_key: Int) (tmp_data: Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH6 : (right = (left + (1 : Int) ))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values_2 (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values_2 (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values_2 (0 : Int)))) (PreH17 : ((Znth current data_values_2 (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values_2 (0 : Int)))) (PreH19 : ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (intArray.full data_pre n_pre (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) )
  **  (intArray.full key_pre n_pre (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))) )
  **  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values_2 (0 : Int))) (current) ((replace_Znth ((Znth current data_values_2 (0 : Int))) (smallest) (pos_values_2)))) )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.undef_seg data_pre n_pre capacity )
|--
  EX pos_values : (List Int), EX data_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ ((0 : Int) <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * (2 : Int) ) + (1 : Int) )) ” 
  &&  “ (right = (left + (1 : Int) )) ” 
  &&  “ ((0 : Int) <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ ((0 : Int) <= right) ” 
  &&  “ ((0 : Int) <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ (tmp_key > (Znth current key_values (0 : Int))) ” 
  &&  “ (tmp_key = (Znth smallest key_values (0 : Int))) ” 
  &&  “ (tmp_data = (Znth smallest data_values (0 : Int))) ” 
  &&  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” 
  &&  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” 
  &&  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre smallest ) ”
  &&  (intArray.full key_pre n_pre key_values )
  **  (intArray.undef_seg key_pre n_pre capacity )
  **  (intArray.full data_pre n_pre data_values )
  **  (intArray.undef_seg data_pre n_pre capacity )
  **  (intArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (tmp_key: Int) (tmp_data: Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH6 : (right = (left + (1 : Int) ))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values_2 (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values_2 (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values_2 (0 : Int)))) (PreH17 : ((Znth current data_values_2 (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values_2 (0 : Int)))) (PreH19 : ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SiftDownState M (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth smallest data_values_2 (0 : Int))) (current) ((replace_Znth ((Znth current data_values_2 (0 : Int))) (smallest) (pos_values_2)))) data_bound_pre n_pre smallest ) ” 
  &&  “ ((Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (0 : Int))) ” 
  &&  “ ((Znth current (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (0 : Int)) < data_bound_pre) ” 
  &&  “ ((0 : Int) <= (Znth current (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (0 : Int))) ” 
  &&  “ (tmp_data = (Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (0 : Int))) ” 
  &&  “ (tmp_key = (Znth smallest (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))) (0 : Int))) ” 
  &&  “ (tmp_key > (Znth current (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))) (0 : Int))) ”
  &&  emp
)

-- Coq source line 1492; retained premise: PreH15.
noncomputable def pqdk_sift_down_entail_wit_5_split_goal_1 : Prop :=
forall (n_pre: Int) (data_bound_pre: Int) (capacity: Int) (M: partial_map) (key_values_2: (List Int)) (data_values_2: (List Int)) (pos_values_2: (List Int)) (current: Int) (left: Int) (right: Int) (smallest: Int) (tmp_key: Int) (tmp_data: Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * (2 : Int) ) + (1 : Int) ))) (PreH6 : (right = (left + (1 : Int) ))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values_2 (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values_2 (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values_2 (0 : Int)))) (PreH17 : ((Znth current data_values_2 (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values_2 (0 : Int)))) (PreH19 : ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SiftDownState M (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth smallest data_values_2 (0 : Int))) (current) ((replace_Znth ((Znth current data_values_2 (0 : Int))) (smallest) (pos_values_2)))) data_bound_pre n_pre smallest )

end SourceVC

theorem pqdk_sift_up_entail_wit_4_iff :
    SourceVC.pqdk_sift_up_entail_wit_4 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_up_entail_wit_4 := by
  unfold SourceVC.pqdk_sift_up_entail_wit_4 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_up_entail_wit_4
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      simpa only [PreH11] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      simpa only [PreH11] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem pqdk_sift_up_entail_wit_4_split_goal_1_iff :
    SourceVC.pqdk_sift_up_entail_wit_4_split_goal_1 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_up_entail_wit_4_split_goal_1 := by
  unfold SourceVC.pqdk_sift_up_entail_wit_4_split_goal_1 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_up_entail_wit_4_split_goal_1
  constructor
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    simpa only [PreH11] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    simpa only [PreH11] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem pqdk_sift_down_entail_wit_3_1_iff :
    SourceVC.pqdk_sift_down_entail_wit_3_1 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_1 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_3_1 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_1
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem pqdk_sift_down_entail_wit_3_1_split_goal_1_iff :
    SourceVC.pqdk_sift_down_entail_wit_3_1_split_goal_1 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_1_split_goal_1 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_3_1_split_goal_1 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_1_split_goal_1
  constructor
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem pqdk_sift_down_entail_wit_3_2_iff :
    SourceVC.pqdk_sift_down_entail_wit_3_2 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_2 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_3_2 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_2
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem pqdk_sift_down_entail_wit_3_2_split_goal_1_iff :
    SourceVC.pqdk_sift_down_entail_wit_3_2_split_goal_1 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_2_split_goal_1 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_3_2_split_goal_1 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_2_split_goal_1
  constructor
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    simpa only [PreH8] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem pqdk_sift_down_entail_wit_3_3_iff :
    SourceVC.pqdk_sift_down_entail_wit_3_3 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_3 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_3_3 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_3
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      simpa only [PreH9] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      simpa only [PreH9] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem pqdk_sift_down_entail_wit_3_3_split_goal_1_iff :
    SourceVC.pqdk_sift_down_entail_wit_3_3_split_goal_1 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_3_split_goal_1 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_3_3_split_goal_1 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_3_3_split_goal_1
  constructor
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    simpa only [PreH9] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    simpa only [PreH9] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem pqdk_sift_down_entail_wit_4_iff :
    SourceVC.pqdk_sift_down_entail_wit_4 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_4 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_4 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_4
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      simpa only [PreH6] using h n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      simpa only [PreH6] using h n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem pqdk_sift_down_entail_wit_4_split_goal_6_iff :
    SourceVC.pqdk_sift_down_entail_wit_4_split_goal_6 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_4_split_goal_6 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_4_split_goal_6 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_4_split_goal_6
  constructor
  · intro h n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    simpa only [PreH6] using h n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  · intro h n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    simpa only [PreH6] using h n_pre data_bound_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem pqdk_sift_down_entail_wit_5_iff :
    SourceVC.pqdk_sift_down_entail_wit_5 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_5 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_5 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_5
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      simpa only [PreH15] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      intro n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
      simpa only [PreH15] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem pqdk_sift_down_entail_wit_5_split_goal_1_iff :
    SourceVC.pqdk_sift_down_entail_wit_5_split_goal_1 ↔ SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_5_split_goal_1 := by
  unfold SourceVC.pqdk_sift_down_entail_wit_5_split_goal_1 SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal.pqdk_sift_down_entail_wit_5_split_goal_1
  constructor
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    simpa only [PreH15] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  · intro h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    simpa only [PreH15] using h n_pre data_bound_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

-- Kernel dependency audit for all source/generated equivalences.
#print axioms pqdk_sift_up_entail_wit_4_iff
#print axioms pqdk_sift_up_entail_wit_4_split_goal_1_iff
#print axioms pqdk_sift_down_entail_wit_3_1_iff
#print axioms pqdk_sift_down_entail_wit_3_1_split_goal_1_iff
#print axioms pqdk_sift_down_entail_wit_3_2_iff
#print axioms pqdk_sift_down_entail_wit_3_2_split_goal_1_iff
#print axioms pqdk_sift_down_entail_wit_3_3_iff
#print axioms pqdk_sift_down_entail_wit_3_3_split_goal_1_iff
#print axioms pqdk_sift_down_entail_wit_4_iff
#print axioms pqdk_sift_down_entail_wit_4_split_goal_6_iff
#print axioms pqdk_sift_down_entail_wit_5_iff
#print axioms pqdk_sift_down_entail_wit_5_split_goal_1_iff

end SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_vc_compat
