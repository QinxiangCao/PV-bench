Require Import PVbench.Algorithms.concatenating_numbers_dp.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

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
  0 <= position <= Zlength lhs /\
  Zlength lhs = Zlength rhs /\
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
Definition BitScanState
    (mask count bit bit_value : Z) : Prop :=
  1 <= mask < Z.shiftl 1 count /\
  0 <= bit <= count /\
  bit_value = Z.shiftl 1 bit /\
  (forall lower,
     0 <= lower < bit -> Z.testbit mask lower = false).
Definition SelectedBitState
    (mask count bit bit_value rest : Z) : Prop :=
  BitScanState mask count bit bit_value /\
  Z.land mask bit_value <> 0 /\
  0 <= bit < count /\
  Z.testbit mask bit = true /\
  rest = Z.lxor mask bit_value /\
  0 <= rest < mask.
Definition MaskIndexes (count mask : Z) (indices : list Z) : Prop :=
  forall index,
    In index indices <->
    0 <= index < count /\ Z.testbit mask index = true.

(* The output loop has consumed [done] and still owns exactly the rows whose
   bits occur in [mask].  The concatenation of [done ++ todo] is a global
   optimum, so this describes a mathematical optimal-prefix state rather
   than an execution trace of the C loop. *)
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

Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.ZArith.Zbitwise.
Require Import Coq.Logic.ClassicalDescription.
