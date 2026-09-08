Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.RelationClasses.
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

(**
  A reusable multiset has exactly one piece of data: an arbitrary list
  representative.  Two representatives denote the same bag precisely when
  they are permutations.  In particular, no array layout or heap-order proof
  is stored in [multiset].
 *)

Record multiset (A : Type) : Type := {
  mlist : list A
}.

Arguments mlist {A} _.

Definition list_to_multiset {A} (l : list A) : multiset A :=
  {| mlist := l |}.

Definition multiset_empty {A} : multiset A :=
  list_to_multiset [].

Definition multiset_size {A} (S : multiset A) : Z :=
  Zlength (mlist S).

Definition multiset_equiv {A} (S1 S2 : multiset A) : Prop :=
  Permutation (mlist S1) (mlist S2).

Definition multiset_insert {A}
    (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (x :: mlist S).

Definition multiset_union {A}
    (S1 S2 : multiset A) : multiset A :=
  list_to_multiset (mlist S1 ++ mlist S2).

Definition multiset_map {A B}
    (f : A -> B) (S : multiset A) : multiset B :=
  list_to_multiset (map f (mlist S)).

Definition multiset_member_by {A}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (S : multiset A) (x : A) : bool :=
  existsb (fun y => if eq_dec x y then true else false)
    (mlist S).

Definition multiset_count_by {A}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (S : multiset A) (x : A) : nat :=
  count_occ eq_dec (mlist S) x.

(**
  Removal is total.  Its public specification below uses [In x (mlist S)] as
  the successful-removal guard directly: exactly one occurrence is removed
  when present, while an absent element leaves the multiset unchanged.
 *)
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

#[export] Instance multiset_equiv_Equivalence (A : Type) :
  Equivalence (@multiset_equiv A).
Proof.
  split.
  - intros S. apply Permutation_refl.
  - intros S1 S2 H. now apply Permutation_sym.
  - intros S1 S2 S3 H12 H23.
    eapply Permutation_trans; eauto.
Qed.

(** Deterministic maximum for nonempty integer multisets. *)

Definition multiset_max (S : multiset Z) : Z :=
  match mlist S with
  | [] => 0
  | x :: xs => fold_right Z.max x xs
  end.

Definition multiset_maximum
    (S : multiset Z) (value : Z) : Prop :=
  In value (mlist S) /\
  forall x,
    In x (mlist S) ->
    x <= value.

(**
  Priority-queue representation.  [heap_relation] is the constructive bridge:
  its [Permutation] proof relates the reusable multiset representative to the
  actual heap-array order.  Heap order belongs here, outside [multiset].
 *)

Definition heap_capacity : Z := 100000.

Definition heap_parent (child : Z) : Z :=
  Z.quot (child - 1) 2.

Definition heap_left_child (index : Z) : Z :=
  index * 2 + 1.

Definition heap_right_child (index : Z) : Z :=
  index * 2 + 2.

Definition heap_selected_child
    (concrete : list Z) (size index : Z) : Z :=
  let left := heap_left_child index in
  let right := heap_right_child index in
  match Z_lt_dec right size with
  | left _ =>
      match
        Z_lt_dec
          (Znth left concrete 0)
          (Znth right concrete 0)
      with
      | left _ => right
      | right _ => left
      end
  | right _ => left
  end.

Definition heap_ordered (concrete : list Z) (size : Z) : Prop :=
  forall child,
    0 < child /\ child < size ->
    Znth (heap_parent child) concrete 0 >= Znth child concrete 0.

Definition heap_relation
    (S : multiset Z) (concrete : list Z) : Prop :=
  Permutation (mlist S) concrete.

Definition heap_representation
    (S : multiset Z) (concrete : list Z) (size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  multiset_size S = size /\
  Zlength concrete = size /\
  heap_relation S concrete /\
  heap_ordered concrete size.

Definition store_heap
    (p : Z) (S : multiset Z) (size : Z) : Assertion :=
  EX concrete : list Z,
    “ heap_representation S concrete size ” &&
    IntArray.full p size concrete.

Definition heap_spare (p size : Z) : Assertion :=
  IntArray.undef_seg p size (size + 1).

Definition heap_retired_cell (p index value : Z) : Assertion :=
  IntArray.seg p index (index + 1) [value].

(**
  Annotation-facing predicates describe the mathematical partial heap facts
  maintained by sift-up, incremental build, and sift-down.  They are relations,
  not executable copies of the C loops.
 *)

Definition PrefixMaximum
    (concrete : list Z) (size value : Z) : Prop :=
  0 < size /\
  size <= Zlength concrete /\
  Znth 0 concrete 0 = value /\
  forall i,
    0 <= i /\ i < size ->
    Znth i concrete 0 <= value.

Definition HeapOrderExceptUp
    (concrete : list Z) (size child : Z) : Prop :=
  0 <= child /\
  child < size /\
  forall node,
    0 < node /\ node < size /\ node <> child ->
    Znth (heap_parent node) concrete 0 >= Znth node concrete 0.

Definition PushHoleChildrenPreserved
    (concrete : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node /\ node < size /\ heap_parent node = child ->
    Znth (heap_parent child) concrete 0 >= Znth node concrete 0.

Definition PushSource
    (written : list Z) (before : multiset Z) (size x : Z) : Prop :=
  Zlength written = size + 1 /\
  Permutation written (x :: mlist before) /\
  heap_ordered (sublist 0 size written) size.

Definition PushLoopState
    (written current : list Z) (size child x : Z) : Prop :=
  0 <= size /\
  Zlength written = size + 1 /\
  Zlength current = size + 1 /\
  0 <= child /\
  child <= size /\
  Znth child current 0 = x /\
  Permutation written current /\
  HeapOrderExceptUp current (size + 1) child /\
  PushHoleChildrenPreserved current (size + 1) child.

Definition PushResult
    (before : multiset Z) (result : list Z) (size x : Z) : Prop :=
  0 <= size /\
  Zlength result = size + 1 /\
  Permutation result (x :: mlist before) /\
  heap_ordered result (size + 1).

Definition BuildPrefixState
    (prefix : multiset Z) (input : list Z) (processed : Z) : Prop :=
  1 <= processed /\
  processed <= Zlength input /\
  multiset_equiv
    prefix
    (list_to_multiset (sublist 0 processed input)).

Definition HeapOrderExceptDown
    (concrete : list Z) (size index : Z) : Prop :=
  0 <= index /\
  index < size /\
  forall child,
    0 < child /\ child < size /\ heap_parent child <> index ->
    Znth (heap_parent child) concrete 0 >= Znth child concrete 0.

Definition PopHoleParentDominatesChildren
    (current : list Z) (size index : Z) : Prop :=
  index = 0 \/
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth (heap_parent index) current 0 >= Znth child current 0.

Definition PopSelectedChild
    (current : list Z) (size index selected : Z) : Prop :=
  0 <= index /\
  index < size /\
  index < selected /\
  0 <= selected /\
  selected < size /\
  heap_parent selected = index /\
  selected = heap_selected_child current size index /\
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth selected current 0 >= Znth child current 0.

Definition PopRemainingElements
    (before current : list Z) (size : Z) : Prop :=
  1 <= size /\
  size <= Zlength before /\
  size <= Zlength current /\
  Permutation
    (sublist 0 (size - 1) current)
    (sublist 1 size before).

Definition PopLoopState
    (before current : list Z) (size index : Z) : Prop :=
  1 < size /\
  Zlength before = size /\
  Zlength current = size /\
  0 <= index /\
  index < size - 1 /\
  heap_ordered before size /\
  Znth index current 0 = Znth (size - 1) before 0 /\
  Znth (size - 1) current 0 = Znth (size - 1) before 0 /\
  PopRemainingElements before current size /\
  HeapOrderExceptDown current (size - 1) index /\
  PopHoleParentDominatesChildren current (size - 1) index.

Definition PopReadyState
    (before current : list Z) (size result : Z) : Prop :=
  1 < size /\
  Zlength before = size /\
  Zlength current = size /\
  heap_ordered before size /\
  PrefixMaximum before size result /\
  Znth (size - 1) current 0 = Znth (size - 1) before 0 /\
  PopRemainingElements before current size /\
  heap_ordered current (size - 1).

Definition PopResult
    (S : multiset Z) (before result : list Z)
    (size value : Z) : Prop :=
  1 <= size /\
  Zlength before = size /\
  Zlength result = size /\
  value = multiset_max S /\
  heap_ordered (sublist 0 (size - 1) result) (size - 1) /\
  Permutation
    (sublist 0 (size - 1) result)
    (mlist (multiset_remove S value)).

(**
  [HeapSortState] is the mathematical state of the in-place heap-sort
  extraction loop.  The still-active priority queue and the retired suffix
  together are a permutation of the original input.  The suffix is already
  nondecreasing, and every active value belongs to the left of every retired
  value in the final ordering.

  This relation deliberately does not describe how [build] or [pop] execute;
  any max-priority-queue implementation satisfying their public contracts can
  be used to establish and preserve it.
 *)
Definition HeapSortState
    (input : list Z) (active : multiset Z) (suffix : list Z) : Prop :=
  Permutation input (mlist active ++ suffix) /\
  increasing suffix /\
  forall active_value suffix_value,
    In active_value (mlist active) ->
    In suffix_value suffix ->
    active_value <= suffix_value.

