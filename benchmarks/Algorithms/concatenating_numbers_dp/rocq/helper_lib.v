Require Export PVbench.Algorithms.concatenating_numbers_dp.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import MaxMinLib.MaxMin.
Require Import SumLib.ZRange.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Local Notation sum := AUXLib.ListLib.sum.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.ZArith.Zbitwise.
Require Import Coq.Logic.ClassicalDescription.
(* The annotation parser emits Zlength as a higher-order argument to map. *)
Arguments Zlength {A}.

Definition item_before_or_equal
    (rows : list (list Z)) (lengths : list Z) (i j : Z) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i)).

Definition FlatRows
    (flat : list Z) (rows : list (list Z)) (count width : Z) : Prop :=
  Zlength flat = count * width /\
  Zlength rows = count /\
  forall i,
    0 <= i < count ->
    Znth i rows nil = sublist (i * width) ((i + 1) * width) flat.

Definition ConcatLeftDigit
    (rows : list (list Z)) (lens : list Z) (i j position : Z) : Z :=
  Znth position
    (item_digits (item_at rows lens i) ++
     item_digits (item_at rows lens j)) 0.

Definition ConcatRightDigit
    (rows : list (list Z)) (lens : list Z) (i j position : Z) : Z :=
  Znth position
    (item_digits (item_at rows lens j) ++
     item_digits (item_at rows lens i)) 0.

Definition ConcatComparePrefix
    (rows : list (list Z)) (lens : list Z)
    (i j position : Z) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j) in
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i) in
  forall k, 0 <= k < position -> Znth k lhs 0 = Znth k rhs 0.

(* Stable semantic state for the comparator scan.  The C locals holding the
   two row lengths are observations of [lens], while [position] records the
   common prefix already compared.  Arithmetic bounds and memory ownership
   remain explicit in the C invariant. *)
Definition ConcatCompareLoopState
    (rows : list (list Z)) (lens : list Z)
    (left right left_length right_length position : Z) : Prop :=
  left_length = Znth left lens 0 /\
  right_length = Znth right lens 0 /\
  ConcatComparePrefix rows lens left right position.

Definition ConcatCompareSignOutcome
    (rows : list (list Z)) (lens : list Z)
    (i j comparison : Z) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j) in
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i) in
  (comparison = 0 /\ lhs = rhs) \/
  (comparison = 1 /\
   exists k,
     0 <= k < Zlength lhs /\
     Zlength lhs = Zlength rhs /\
     (forall p, 0 <= p < k -> Znth p lhs 0 = Znth p rhs 0) /\
     Znth k rhs 0 < Znth k lhs 0) \/
  (comparison = -1 /\
   exists k,
     0 <= k < Zlength lhs /\
     Zlength lhs = Zlength rhs /\
     (forall p, 0 <= p < k -> Znth p lhs 0 = Znth p rhs 0) /\
     Znth k lhs 0 < Znth k rhs 0).

Definition BestIndexForMask
    (rows : list (list Z)) (lens : list Z)
    (count mask index : Z) : Prop :=
  max_value_of_subset
    (fun i j => item_before_or_equal rows lens j i)
    (fun i => 0 <= i < count /\ Z.testbit mask i = true)
    (fun i : Z => i) index.

(* A semantic table invariant: every materialized nonzero mask stores a
   mathematically greatest first row for that selected subset. *)
Definition DPTablePrefix
    (rows : list (list Z)) (lens : list Z) (count computed : Z)
    (choices : list Z) : Prop :=
  Znth 0 choices 0 = -1 /\
  forall mask,
    1 <= mask < computed ->
    BestIndexForMask rows lens count mask (Znth mask choices 0).

Definition BitScanState
    (mask count bit bit_value : Z) : Prop :=
  bit_value = Z.shiftl 1 bit /\
  (forall lower,
     0 <= lower < bit -> Z.testbit mask lower = false).

Definition SelectedBitState
    (mask count bit bit_value rest : Z) : Prop :=
  BitScanState mask count bit bit_value /\
  Z.land mask bit_value <> 0 /\
  Z.testbit mask bit = true /\
  rest = Z.lxor mask bit_value.

Definition MaskIndexes (count mask : Z) (indices : list Z) : Prop :=
  forall index,
    In index indices <->
    0 <= index < count /\ Z.testbit mask index = true.

Definition GreedyOutputPrefix
    (rows : list (list Z)) (lens : list Z)
    (count mask : Z) (output : list Z) : Prop :=
  exists done todo,
    Permutation (all_indices count) (done ++ todo) /\
    MaskIndexes count mask todo /\
    output = concatenate_indices rows lens done /\
    LargestConcatenation rows lens
      (concatenate_indices rows lens (done ++ todo)).

Definition AppendRowPrefix
    (rows : list (list Z)) (lens : list Z)
    (prior : list Z) (index position : Z) (current : list Z) : Prop :=
  current = prior ++
    sublist 0 position (item_digits (item_at rows lens index)).
