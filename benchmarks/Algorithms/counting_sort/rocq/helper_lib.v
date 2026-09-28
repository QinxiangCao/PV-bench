Require Export PVbench.Algorithms.counting_sort.rocq.spec_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Sorting.Permutation.
Require Import SumLib.Sum SumLib.ZRange.
From AUXLib Require Import ListLib MonotonicList.
From Coq Require Import Lia.

(** Mixed local storage has [Some 0] in every initialized histogram cell. *)
Definition CountingZeroedPrefix
    (mixed_counts : list (option Z)) (upto : Z) : Prop :=
  Forall (eq (Some 0)) (sublist 0 upto mixed_counts).

(** The canonical number of occurrences of [value] in a mathematical list. *)
Definition CountingFrequency (values : list Z) (value : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec values value).

(** The exact histogram of the already scanned input prefix. *)
Definition CountingHistogramPrefix
    (input counts : list Z) (processed : Z) : Prop :=
  forall value,
    0 <= value < 100 ->
    Znth value counts 0 =
      CountingFrequency (sublist 0 processed input) value.

(** The canonical inclusive end of one value bucket. *)
Definition CountingCumulativeEnd (input : list Z) (value : Z) : Z :=
  Sum.sum (fun bucket : Z => 0 <= bucket < value + 1)
          (CountingFrequency input).

(** During prefix summation, lower buckets already hold cumulative ends and
    the remaining buckets still hold raw whole-input frequencies. *)
Definition CountingCumulativeState
    (input positions : list Z) (next_value : Z) : Prop :=
  forall value,
    0 <= value < 100 ->
    Znth value positions 0 =
      if value <? next_value
      then CountingCumulativeEnd input value
      else CountingFrequency input value.

(** The implementation-independent mathematical result needed by the frozen
    sort contract. *)
Definition CountingSorted (input sorted : list Z) : Prop :=
  Permutation input sorted /\
  increasing sorted.

Definition CountingBucketStart (input : list Z) (value : Z) : Z :=
  if value <=? 0
  then 0
  else CountingCumulativeEnd input (value - 1).

Definition CountingPlacementProgress
    (input positions bucket_ends : list Z)
    (mixed_output : list (option Z)) (sorted : list Z)
    (next_index : Z) : Prop :=
  CountingSorted input sorted /\
  (forall value,
    0 <= value < 100 ->
    Znth value bucket_ends 0 =
      CountingCumulativeEnd input value) /\
  (forall value,
    0 <= value < 100 ->
    Znth value positions 0 =
      CountingBucketStart input value +
      CountingFrequency (sublist 0 (next_index + 1) input) value) /\
  (forall value,
    0 <= value < 100 ->
    Forall2 (fun cell value => cell = Some value)
      (map (fun index => Znth index mixed_output None)
        (Zrange (Znth value positions 0) (Znth value bucket_ends 0)))
      (map (fun index => Znth index sorted 0)
        (Zrange (Znth value positions 0) (Znth value bucket_ends 0)))).

(** Sequential copy-back state: exactly the target prefix has been written,
    and the untouched suffix still comes from the original input. *)
Definition CountingCopyProgress
    (before target live : list Z) (copied : Z) : Prop :=
  live =
    app
      (sublist 0 copied target)
      (sublist copied (Zlength before) before).
