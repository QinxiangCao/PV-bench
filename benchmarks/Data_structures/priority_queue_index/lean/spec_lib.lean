import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import AUXLib.Arithmetic
import AUXLib.ListLib.LengthCompat

namespace Data_structures.priority_queue_index.lean

open AUXLib AUXLib.Sorting

open SimpleC.SL.CNotation SimpleC.SL.CommonAssertion

open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig

open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic

open scoped SimpleC.SL.SAC

local instance : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev intArray := naive_C_Rules.IntArray

structure multiset (A : Type) where
  Build_multiset ::
  mlist : List A

export multiset (mlist)

@[match_pattern] abbrev Build_multiset (A : Type) (mlist : List A) : multiset A := multiset.Build_multiset mlist

def list_to_multiset {A : Type} (l : List A) : multiset A := ⟨l⟩

def multiset_size {A : Type} (S : multiset A) : Int := Zlength (mlist S)

def multiset_equiv {A : Type} (S1 S2 : multiset A) : Prop := Permutation (mlist S1) (mlist S2)

def multiset_insert {A : Type} (S : multiset A) (x : A) : multiset A := list_to_multiset (x :: mlist S)

noncomputable def multiset_remove {A : Type} (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (remove_one (mlist S))
where
  remove_one : List A → List A
    | [] => []
    | y :: ys => @ite (List A) (x = y) (Classical.propDecidable _) ys (y :: remove_one ys)

def heap_item (key data : Int) : Int × Int := (key,data)

def item_key (item : Int × Int) : Int := item.1

def item_data (item : Int × Int) : Int := item.2

def pair_list (key_values data_values : List Int) : List (Int × Int) := key_values.zip data_values

def multiset_min (S : multiset (Int × Int)) : Int × Int :=
  match mlist S with
  | [] => heap_item 0 0
  | x :: xs => xs.foldr (fun y best => if item_key y ≤ item_key best then y else best) x

def multiset_minimum (S : multiset (Int × Int)) (item : Int × Int) : Prop :=
  item ∈ mlist S ∧ ∀ x, x ∈ mlist S → item_key item ≤ item_key x

def heap_capacity : Int := 100000

def heap_parent (child : Int) : Int := Z.quot (child - 1) 2

def heap_left_child (index : Int) : Int := index * 2 + 1

def heap_right_child (index : Int) : Int := index * 2 + 2

def heap_selected_child (key_values : List Int) (size index : Int) : Int :=
  let left := heap_left_child index
  let right := heap_right_child index
  if right < size then
    if Znth left key_values 0 ≤ Znth right key_values 0 then left else right
  else left

def heap_relation (S : multiset (Int × Int)) (key_values data_values : List Int) : Prop :=
  Permutation (mlist S) (pair_list key_values data_values)

def heap_ordered (key_values : List Int) (size : Int) : Prop :=
  ∀ child, (0 < child ∧ child < size) → Znth (heap_parent child) key_values 0 ≤ Znth child key_values 0

def heap_representation (S : multiset (Int × Int)) (key_values data_values : List Int) (size : Int) : Prop :=
  0 ≤ size ∧ size ≤ heap_capacity ∧ multiset_size S = size ∧ Zlength key_values = size ∧
  Zlength data_values = size ∧ heap_relation S key_values data_values ∧ heap_ordered key_values size

noncomputable def heap_spare (p size : Int) : Assertion := intArray.undef_seg p size (size + 1)

noncomputable def heap_tail (p size : Int) : Assertion :=
  if size < heap_capacity then heap_spare p size ** intArray.undef_seg p (size+1) heap_capacity
  else intArray.undef_seg p size heap_capacity

noncomputable def store_heap (key data : Int) (S : multiset (Int × Int)) (size : Int) : Assertion :=
  EX key_values : List Int, EX data_values : List Int,
    “ heap_representation S key_values data_values size ” &&
    (intArray.full key size key_values ** heap_tail key size ** intArray.full data size data_values ** heap_tail data size)

noncomputable def heap_retired_pair (key data index : Int) (item : Int × Int) : Assertion :=
  intArray.seg key index (index+1) [item_key item] ** intArray.seg data index (index+1) [item_data item]

def KeyWriteState (before : multiset (Int × Int)) (key_base data_base key_written : List Int) (size key_x : Int) : Prop :=
  heap_representation before key_base data_base size ∧ key_written = key_base ++ [key_x]

def HeapOrderExceptUp (key_values : List Int) (size child : Int) : Prop :=
  0 ≤ child ∧ child < size ∧ ∀ node, (0 < node ∧ node < size ∧ node ≠ child) →
    Znth (heap_parent node) key_values 0 ≤ Znth node key_values 0

def PushHoleChildrenPreserved (key_values : List Int) (size child : Int) : Prop :=
  ∀ node, (0 < node ∧ node < size ∧ heap_parent node = child) →
    Znth (heap_parent child) key_values 0 ≤ Znth node key_values 0

def PushSource (key_written data_written : List Int) (before : multiset (Int × Int)) (size data_x key_x : Int) : Prop :=
  Zlength key_written = size+1 ∧ Zlength data_written = size+1 ∧
  Permutation (pair_list key_written data_written) (heap_item key_x data_x :: mlist before) ∧
  heap_ordered (sublist 0 size key_written) size

def PushLoopState (key_written data_written key_current data_current : List Int) (size child data_x key_x : Int) : Prop :=
  0 ≤ size ∧ Zlength key_written = size+1 ∧ Zlength data_written = size+1 ∧
  Zlength key_current = size+1 ∧ Zlength data_current = size+1 ∧ 0 ≤ child ∧ child ≤ size ∧
  Znth child key_current 0 = key_x ∧ Znth child data_current 0 = data_x ∧
  Permutation (pair_list key_written data_written) (pair_list key_current data_current) ∧
  HeapOrderExceptUp key_current (size+1) child ∧ PushHoleChildrenPreserved key_current (size+1) child

def PushResult (before : multiset (Int × Int)) (key_result data_result : List Int) (size data_x key_x : Int) : Prop :=
  0 ≤ size ∧ Zlength key_result = size+1 ∧ Zlength data_result = size+1 ∧
  Permutation (pair_list key_result data_result) (heap_item key_x data_x :: mlist before) ∧
  heap_ordered key_result (size+1)

def BuildPrefixState («prefix» : multiset (Int × Int)) (key_input data_input : List Int) (processed : Int) : Prop :=
  1 ≤ processed ∧ processed ≤ Zlength key_input ∧ processed ≤ Zlength data_input ∧
  multiset_equiv «prefix» (list_to_multiset (pair_list (sublist 0 processed key_input) (sublist 0 processed data_input)))

def PrefixMinimum (key_values data_values : List Int) (size : Int) (item : Int × Int) : Prop :=
  0 < size ∧ size ≤ Zlength key_values ∧ size ≤ Zlength data_values ∧
  item = heap_item (Znth 0 key_values 0) (Znth 0 data_values 0) ∧
  ∀ i, (0 ≤ i ∧ i < size) → item_key item ≤ Znth i key_values 0

def HeapOrderExceptDown (key_values : List Int) (size index : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ ∀ child, (0 < child ∧ child < size ∧ heap_parent child ≠ index) →
  Znth (heap_parent child) key_values 0 ≤ Znth child key_values 0

def PopHoleParentDominatesChildren (key_values : List Int) (size index : Int) : Prop :=
  index = 0 ∨ ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) →
    Znth (heap_parent index) key_values 0 ≤ Znth child key_values 0

def PopSelectedChild (key_values : List Int) (size index selected : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ index < selected ∧ 0 ≤ selected ∧ selected < size ∧
  heap_parent selected = index ∧ selected = heap_selected_child key_values size index ∧
  ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) → Znth selected key_values 0 ≤ Znth child key_values 0

def PopRemainingElements (before_key before_data current_key current_data : List Int) (size : Int) : Prop :=
  1 ≤ size ∧ size ≤ Zlength before_key ∧ size ≤ Zlength before_data ∧
  size ≤ Zlength current_key ∧ size ≤ Zlength current_data ∧
  Permutation (pair_list (sublist 0 (size-1) current_key) (sublist 0 (size-1) current_data))
    (pair_list (sublist 1 size before_key) (sublist 1 size before_data))

def PopLoopState (before_key before_data current_key current_data : List Int) (size index : Int) : Prop :=
  1 < size ∧ Zlength before_key = size ∧ Zlength before_data = size ∧
  Zlength current_key = size ∧ Zlength current_data = size ∧ 0 ≤ index ∧ index < size-1 ∧
  heap_ordered before_key size ∧ Znth index current_key 0 = Znth (size-1) before_key 0 ∧
  Znth index current_data 0 = Znth (size-1) before_data 0 ∧
  PopRemainingElements before_key before_data current_key current_data size ∧
  HeapOrderExceptDown current_key (size-1) index ∧ PopHoleParentDominatesChildren current_key (size-1) index

def PopReadyState (before_key before_data current_key current_data : List Int) (size : Int) (item : Int × Int) : Prop :=
  1 < size ∧ Zlength before_key = size ∧ Zlength before_data = size ∧ Zlength current_key = size ∧
  Zlength current_data = size ∧ heap_ordered before_key size ∧ PrefixMinimum before_key before_data size item ∧
  PopRemainingElements before_key before_data current_key current_data size ∧ heap_ordered current_key (size-1)

def PopResult (S : multiset (Int × Int)) (before_key before_data result_key result_data : List Int) (size : Int) (item : Int × Int) : Prop :=
  1 ≤ size ∧ Zlength before_key = size ∧ Zlength before_data = size ∧ Zlength result_key = size ∧
  Zlength result_data = size ∧ heap_ordered (sublist 0 (size-1) result_key) (size-1) ∧
  Permutation (pair_list (sublist 0 (size-1) result_key) (sublist 0 (size-1) result_data)) (mlist (multiset_remove S item))

end Data_structures.priority_queue_index.lean
