Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition heap_capacity : Z := 100000.
Definition absent : Z := -1.

Definition heap_item (key data : Z) : Z * Z := (key, data).
Definition item_key (item : Z * Z) : Z := fst item.
Definition item_data (item : Z * Z) : Z := snd item.

Definition pair_list (key_values data_values : list Z) : list (Z * Z) :=
  combine key_values data_values.

Definition partial_map : Type := Z -> option Z.

Definition partial_map_get (M : partial_map) (data_x : Z) : option Z :=
  M data_x.

Definition partial_map_add
    (M : partial_map) (data_x key_x : Z) : partial_map :=
  fun query =>
    if Z.eq_dec query data_x then Some key_x else M query.

Definition partial_map_update
    (M : partial_map) (data_x key_x : Z) : partial_map :=
  partial_map_add M data_x key_x.

Definition partial_map_update_or_add
    (M : partial_map) (data_x key_x : Z) : partial_map :=
  partial_map_update M data_x key_x.

Definition partial_map_remove
    (M : partial_map) (data_x : Z) : partial_map :=
  fun query =>
    if Z.eq_dec query data_x then None else M query.

Definition partial_map_absent (M : partial_map) (data_x : Z) : Prop :=
  partial_map_get M data_x = None.

Definition partial_map_present
    (M : partial_map) (data_x key_x : Z) : Prop :=
  partial_map_get M data_x = Some key_x.

Definition partial_map_contains
    (M : partial_map) (data_x : Z) : Prop :=
  exists key_x, partial_map_present M data_x key_x.

Definition partial_map_item (M : partial_map) (item : Z * Z) : Prop :=
  partial_map_present M (item_data item) (item_key item).

Definition partial_map_minimum (M : partial_map) (item : Z * Z) : Prop :=
  partial_map_item M item /\
  forall data_x key_x,
    partial_map_present M data_x key_x ->
    item_key item <= key_x.

Definition heap_data_at
    (data_values : list Z) (index data_x : Z) : Prop :=
  0 <= index < Zlength data_values /\
  Znth index data_values 0 = data_x.

Definition heap_contains_data
    (M : partial_map) (data_x : Z) : Prop :=
  partial_map_contains M data_x.

Definition heap_data_absent
    (M : partial_map) (data_x : Z) : Prop :=
  partial_map_absent M data_x.

Definition heap_data_present
    (M : partial_map) (data_x : Z) : Prop :=
  heap_contains_data M data_x.

Definition heap_key_of
    (M : partial_map) (data_x key_x : Z) : Prop :=
  partial_map_present M data_x key_x.

Definition heap_data_valid
    (data_values : list Z) (data_bound size : Z) : Prop :=
  forall index,
    0 <= index < size ->
    0 <= Znth index data_values 0 < data_bound.

Definition heap_data_unique
    (data_values : list Z) (size : Z) : Prop :=
  forall i j,
    0 <= i < size ->
    0 <= j < size ->
    Znth i data_values 0 = Znth j data_values 0 ->
    i = j.

Definition heap_map_relation
    (M : partial_map)
    (key_values data_values : list Z) (size : Z) : Prop :=
  Zlength key_values = size /\
  Zlength data_values = size /\
  heap_data_unique data_values size /\
  (forall index,
    0 <= index < size ->
    partial_map_present
      M
      (Znth index data_values 0)
      (Znth index key_values 0)) /\
  (forall data_x key_x,
    partial_map_present M data_x key_x ->
    exists index,
      0 <= index < size /\
      Znth index data_values 0 = data_x /\
      Znth index key_values 0 = key_x).

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

Definition heap_ordered (key_values : list Z) (size : Z) : Prop :=
  forall child,
    0 < child /\ child < size ->
    Znth (heap_parent child) key_values 0 <= Znth child key_values 0.

Definition heap_pos_backlinks
    (data_values pos_values : list Z) (size : Z) : Prop :=
  forall index,
    0 <= index < size ->
    Znth (Znth index data_values 0) pos_values absent = index.

Definition heap_pos_forward_links
    (data_values pos_values : list Z) (data_bound size : Z) : Prop :=
  forall data_x,
    0 <= data_x < data_bound ->
    Znth data_x pos_values absent = absent \/
    exists index,
      0 <= index < size /\
      Znth index data_values 0 = data_x /\
      Znth data_x pos_values absent = index.

Definition heap_pos_consistent
    (data_values pos_values : list Z) (data_bound size : Z) : Prop :=
  0 <= data_bound /\
  Zlength pos_values = data_bound /\
  heap_data_valid data_values data_bound size /\
  heap_pos_backlinks data_values pos_values size /\
  heap_pos_forward_links data_values pos_values data_bound size.

Definition heap_representation
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  heap_map_relation M key_values data_values size /\
  heap_ordered key_values size /\
  heap_pos_consistent data_values pos_values data_bound size.

Definition store_heap
    (key data pos : addr) (data_bound capacity : Z)
    (M : partial_map) (size : Z) : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
  EX pos_values : list Z,
    “ heap_representation
        M key_values data_values pos_values data_bound size ” &&
    IntArray.full key size key_values **
    IntArray.undef_seg key size capacity **
    IntArray.full data size data_values **
    IntArray.undef_seg data size capacity **
    IntArray.full pos data_bound pos_values.

Definition heap_index_of
    (M : partial_map)
    (data_values pos_values : list Z) (data_x index : Z) : Prop :=
  heap_data_present M data_x /\
  0 <= index < Zlength data_values /\
  Znth index data_values 0 = data_x /\
  Znth data_x pos_values absent = index.

Definition decrease_key_pre
    (M : partial_map) (data_x key_x : Z) : Prop :=
  exists old_key,
    heap_key_of M data_x old_key /\
    key_x <= old_key.

Definition partial_map_decrease_key_pre :=
  decrease_key_pre.

Definition update_or_push_pre
    (M : partial_map) (data_x key_x : Z) : Prop :=
  heap_data_absent M data_x \/
  decrease_key_pre M data_x key_x.

Definition partial_map_update_or_add_pre :=
  update_or_push_pre.

Definition partial_map_update_or_add_size
    (before : partial_map)
    (size_before size_after data_x key_x : Z) : Prop :=
  (partial_map_absent before data_x /\
   size_after = size_before + 1) \/
  (partial_map_decrease_key_pre before data_x key_x /\
   size_after = size_before).

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

Definition SelectedChild
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

Definition HeapArrayState
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  heap_map_relation M key_values data_values size /\
  heap_pos_consistent data_values pos_values data_bound size.

Definition SiftUpState
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size child : Z) : Prop :=
  HeapArrayState M key_values data_values pos_values data_bound size /\
  0 <= child < size /\
  HeapOrderExceptUp key_values size child /\
  PushHoleChildrenPreserved key_values size child.

Definition SiftDownState
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size index : Z) : Prop :=
  HeapArrayState M key_values data_values pos_values data_bound size /\
  0 <= index < size /\
  HeapOrderExceptDown key_values size index /\
  PopHoleParentDominatesChildren key_values size index.

Definition store_sift_up
    (key data pos : addr) (data_bound capacity : Z)
    (M : partial_map) (size index : Z) : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
  EX pos_values : list Z,
    “ SiftUpState
        M key_values data_values pos_values data_bound size index ” &&
    IntArray.full key size key_values **
    IntArray.undef_seg key size capacity **
    IntArray.full data size data_values **
    IntArray.undef_seg data size capacity **
    IntArray.full pos data_bound pos_values.

Definition store_sift_down
    (key data pos : addr) (data_bound capacity : Z)
    (M : partial_map) (size index : Z) : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
  EX pos_values : list Z,
    “ SiftDownState
        M key_values data_values pos_values data_bound size index ” &&
    IntArray.full key size key_values **
    IntArray.undef_seg key size capacity **
    IntArray.full data size data_values **
    IntArray.undef_seg data size capacity **
    IntArray.full pos data_bound pos_values.

Definition PushWriteState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size data_x key_x : Z) : Prop :=
  partial_map_absent before data_x /\
  SiftUpState (partial_map_add before data_x key_x)
    key_values data_values pos_values
    data_bound (size + 1) size /\
  Znth size key_values 0 = key_x /\
  Znth size data_values 0 = data_x /\
  Znth data_x pos_values absent = size.

Definition DecreaseKeyWriteState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size data_x key_x index : Z) : Prop :=
  0 <= index < size /\
  Znth index data_values 0 = data_x /\
  partial_map_decrease_key_pre before data_x key_x /\
  SiftUpState (partial_map_update before data_x key_x)
    key_values data_values pos_values
    data_bound size index /\
  Znth index key_values 0 = key_x.

Definition PopRootState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) (popped : Z * Z) : Prop :=
  1 <= size /\
  partial_map_minimum before popped /\
  heap_representation
    (partial_map_remove before (item_data popped))
    key_values data_values pos_values data_bound (size - 1).

Definition heap_pos_backlinks_except
    (data_values pos_values : list Z) (size skipped_index : Z) : Prop :=
  forall index,
    0 <= index < size ->
    index <> skipped_index ->
    Znth (Znth index data_values 0) pos_values absent = index.

Definition PopMarkedState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) (popped : Z * Z) : Prop :=
  1 <= size /\
  partial_map_minimum before popped /\
  0 <= size /\
  size <= heap_capacity /\
  heap_map_relation before key_values data_values size /\
  heap_ordered key_values size /\
  0 <= data_bound /\
  Zlength pos_values = data_bound /\
  heap_data_valid data_values data_bound size /\
  heap_pos_backlinks_except data_values pos_values size 0 /\
  heap_pos_forward_links data_values pos_values data_bound size /\
  Znth 0 key_values 0 = item_key popped /\
  Znth 0 data_values 0 = item_data popped /\
  Znth (item_data popped) pos_values absent = absent /\
  0 <= item_data popped < data_bound.

Definition pop_replaced_values (size : Z) (values : list Z) : list Z :=
  sublist 0 (size - 1)
    (replace_Znth 0 (Znth (size - 1) values 0) values).

Definition pop_replacement_source (size index : Z) : Z :=
  if Z.eq_dec index 0 then size - 1 else index.

Definition heap_swap_values (i j : Z) (values : list Z) : list Z :=
  replace_Znth j (Znth i values 0)
    (replace_Znth i (Znth j values 0) values).

Definition heap_swap_pos
    (data_values pos_values : list Z) (i j : Z) : list Z :=
  replace_Znth (Znth j data_values 0) i
    (replace_Znth (Znth i data_values 0) j pos_values).

Definition swap_source (i j k : Z) : Z :=
  if Z.eq_dec k i then j else if Z.eq_dec k j then i else k.

