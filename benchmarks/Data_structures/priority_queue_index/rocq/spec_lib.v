Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ClassicalDescription.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Record multiset (A : Type) : Type := {
  mlist : list A
}.

Arguments mlist {A} _.

Definition list_to_multiset {A} (l : list A) : multiset A :=
  {| mlist := l |}.

Definition multiset_size {A} (S : multiset A) : Z :=
  Zlength (mlist S).

Definition multiset_equiv {A} (S1 S2 : multiset A) : Prop :=
  Permutation (mlist S1) (mlist S2).

Definition multiset_insert {A}
    (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (x :: mlist S).

Definition multiset_remove {A}
    (S : multiset A) (x : A) : multiset A :=
  let fix remove_one (l : list A) : list A :=
    match l with
    | [] => []
    | y :: ys =>
        if excluded_middle_informative (x = y)
        then ys
        else y :: remove_one ys
    end
  in list_to_multiset (remove_one (mlist S)).

Definition heap_item (key data : Z) : Z * Z := (key, data).

Definition item_key (item : Z * Z) : Z := fst item.

Definition item_data (item : Z * Z) : Z := snd item.

Definition pair_list (key_values data_values : list Z) : list (Z * Z) :=
  combine key_values data_values.

Definition multiset_min (S : multiset (Z * Z)) : Z * Z :=
  match mlist S with
  | [] => heap_item 0 0
  | x :: xs =>
      fold_right
        (fun y best =>
          if Z.leb (item_key y) (item_key best) then y else best)
        x xs
  end.

Definition multiset_minimum
    (S : multiset (Z * Z)) (item : Z * Z) : Prop :=
  In item (mlist S) /\
  forall x,
    In x (mlist S) ->
    item_key item <= item_key x.

Definition heap_capacity : Z := 100000.

Definition heap_parent (child : Z) : Z :=
  Z.quot (child - 1) 2.

Definition heap_left_child (index : Z) : Z :=
  index * 2 + 1.

Definition heap_right_child (index : Z) : Z :=
  index * 2 + 2.

Definition heap_selected_child
    (key_values : list Z) (size index : Z) : Z :=
  let left := heap_left_child index in
  let right := heap_right_child index in
  match Z_lt_dec right size with
  | left _ =>
      if Z.leb (Znth left key_values 0) (Znth right key_values 0)
      then left
      else right
  | right _ => left
  end.

Definition heap_relation
    (S : multiset (Z * Z)) (key_values data_values : list Z) : Prop :=
  Permutation (mlist S) (pair_list key_values data_values).

Definition heap_ordered (key_values : list Z) (size : Z) : Prop :=
  forall child,
    0 < child /\ child < size ->
    Znth (heap_parent child) key_values 0 <= Znth child key_values 0.

Definition heap_representation
    (S : multiset (Z * Z))
    (key_values data_values : list Z) (size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  multiset_size S = size /\
  Zlength key_values = size /\
  Zlength data_values = size /\
  heap_relation S key_values data_values /\
  heap_ordered key_values size.

Definition heap_spare (p size : Z) : Assertion :=
  IntArray.undef_seg p size (size + 1).

Definition heap_tail (p size : Z) : Assertion :=
  match Z_lt_dec size heap_capacity with
  | left _ =>
      heap_spare p size **
      IntArray.undef_seg p (size + 1) heap_capacity
  | right _ =>
      IntArray.undef_seg p size heap_capacity
  end.

Definition store_heap
    (key data : addr) (S : multiset (Z * Z)) (size : Z)
    : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
    “ heap_representation S key_values data_values size ” &&
    IntArray.full key size key_values **
    heap_tail key size **
    IntArray.full data size data_values **
    heap_tail data size.

Definition heap_retired_pair
    (key data index : Z) (item : Z * Z) : Assertion :=
  IntArray.seg key index (index + 1) [item_key item] **
  IntArray.seg data index (index + 1) [item_data item].

Definition KeyWriteState
    (before : multiset (Z * Z))
    (key_base data_base key_written : list Z)
    (size key_x : Z) : Prop :=
  heap_representation before key_base data_base size /\
  key_written = key_base ++ [key_x].

Definition HeapOrderExceptUp
    (key_values : list Z) (size child : Z) : Prop :=
  0 <= child /\
  child < size /\
  forall node,
    0 < node /\ node < size /\ node <> child ->
    Znth (heap_parent node) key_values 0 <= Znth node key_values 0.

Definition PushHoleChildrenPreserved
    (key_values : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node /\ node < size /\ heap_parent node = child ->
    Znth (heap_parent child) key_values 0 <= Znth node key_values 0.

Definition PushSource
    (key_written data_written : list Z)
    (before : multiset (Z * Z))
    (size data_x key_x : Z) : Prop :=
  Zlength key_written = size + 1 /\
  Zlength data_written = size + 1 /\
  Permutation
    (pair_list key_written data_written)
    (heap_item key_x data_x :: mlist before) /\
  heap_ordered (sublist 0 size key_written) size.

Definition PushLoopState
    (key_written data_written key_current data_current : list Z)
    (size child data_x key_x : Z) : Prop :=
  0 <= size /\
  Zlength key_written = size + 1 /\
  Zlength data_written = size + 1 /\
  Zlength key_current = size + 1 /\
  Zlength data_current = size + 1 /\
  0 <= child /\
  child <= size /\
  Znth child key_current 0 = key_x /\
  Znth child data_current 0 = data_x /\
  Permutation
    (pair_list key_written data_written)
    (pair_list key_current data_current) /\
  HeapOrderExceptUp key_current (size + 1) child /\
  PushHoleChildrenPreserved key_current (size + 1) child.

Definition PushResult
    (before : multiset (Z * Z))
    (key_result data_result : list Z)
    (size data_x key_x : Z) : Prop :=
  0 <= size /\
  Zlength key_result = size + 1 /\
  Zlength data_result = size + 1 /\
  Permutation
    (pair_list key_result data_result)
    (heap_item key_x data_x :: mlist before) /\
  heap_ordered key_result (size + 1).

Definition BuildPrefixState
    (prefix : multiset (Z * Z))
    (key_input data_input : list Z) (processed : Z) : Prop :=
  1 <= processed /\
  processed <= Zlength key_input /\
  processed <= Zlength data_input /\
  multiset_equiv
    prefix
    (list_to_multiset
      (pair_list
        (sublist 0 processed key_input)
        (sublist 0 processed data_input))).

Definition PrefixMinimum
    (key_values data_values : list Z)
    (size : Z) (item : Z * Z) : Prop :=
  0 < size /\
  size <= Zlength key_values /\
  size <= Zlength data_values /\
  item = heap_item (Znth 0 key_values 0) (Znth 0 data_values 0) /\
  forall i,
    0 <= i /\ i < size ->
    item_key item <= Znth i key_values 0.

Definition HeapOrderExceptDown
    (key_values : list Z) (size index : Z) : Prop :=
  0 <= index /\
  index < size /\
  forall child,
    0 < child /\ child < size /\ heap_parent child <> index ->
    Znth (heap_parent child) key_values 0 <= Znth child key_values 0.

Definition PopHoleParentDominatesChildren
    (key_values : list Z) (size index : Z) : Prop :=
  index = 0 \/
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth (heap_parent index) key_values 0 <= Znth child key_values 0.

Definition PopSelectedChild
    (key_values : list Z) (size index selected : Z) : Prop :=
  0 <= index /\
  index < size /\
  index < selected /\
  0 <= selected /\
  selected < size /\
  heap_parent selected = index /\
  selected = heap_selected_child key_values size index /\
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth selected key_values 0 <= Znth child key_values 0.

Definition PopRemainingElements
    (before_key before_data current_key current_data : list Z)
    (size : Z) : Prop :=
  1 <= size /\
  size <= Zlength before_key /\
  size <= Zlength before_data /\
  size <= Zlength current_key /\
  size <= Zlength current_data /\
  Permutation
    (pair_list
      (sublist 0 (size - 1) current_key)
      (sublist 0 (size - 1) current_data))
    (pair_list
      (sublist 1 size before_key)
      (sublist 1 size before_data)).

Definition PopLoopState
    (before_key before_data current_key current_data : list Z)
    (size index : Z) : Prop :=
  1 < size /\
  Zlength before_key = size /\
  Zlength before_data = size /\
  Zlength current_key = size /\
  Zlength current_data = size /\
  0 <= index /\
  index < size - 1 /\
  heap_ordered before_key size /\
  Znth index current_key 0 = Znth (size - 1) before_key 0 /\
  Znth index current_data 0 = Znth (size - 1) before_data 0 /\
  PopRemainingElements before_key before_data current_key current_data size /\
  HeapOrderExceptDown current_key (size - 1) index /\
  PopHoleParentDominatesChildren current_key (size - 1) index.

Definition PopReadyState
    (before_key before_data current_key current_data : list Z)
    (size : Z) (item : Z * Z) : Prop :=
  1 < size /\
  Zlength before_key = size /\
  Zlength before_data = size /\
  Zlength current_key = size /\
  Zlength current_data = size /\
  heap_ordered before_key size /\
  PrefixMinimum before_key before_data size item /\
  PopRemainingElements before_key before_data current_key current_data size /\
  heap_ordered current_key (size - 1).

Definition PopResult
    (S : multiset (Z * Z))
    (before_key before_data result_key result_data : list Z)
    (size : Z) (item : Z * Z) : Prop :=
  1 <= size /\
  Zlength before_key = size /\
  Zlength before_data = size /\
  Zlength result_key = size /\
  Zlength result_data = size /\
  heap_ordered (sublist 0 (size - 1) result_key) (size - 1) /\
  Permutation
    (pair_list
      (sublist 0 (size - 1) result_key)
      (sublist 0 (size - 1) result_data))
    (mlist (multiset_remove S item)).

