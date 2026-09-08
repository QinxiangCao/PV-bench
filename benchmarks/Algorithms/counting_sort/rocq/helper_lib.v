From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Sorting.Permutation.
From AUXLib Require Import ListLib.

Definition CountingZeroedPrefix
    (mixed_counts : list (option Z)) (upto : Z) : Prop :=
  forall value,
    0 <= value < upto ->
    Znth value mixed_counts None = Some 0.

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
  fold_right Z.add 0
    (map
      (fun index : nat =>
        CountingFrequency input (Z.of_nat index))
      (seq 0 (Z.to_nat (value + 1)))).

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

(** Reverse traversal fills a suffix of every value bucket.  [positions]
    marks each still-unfilled bucket prefix; [mixed_output] records the cells
    already known to agree with the mathematical sorted result. *)
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
  (forall value index,
    0 <= value < 100 ->
    Znth value positions 0 <= index < Znth value bucket_ends 0 ->
    Znth index mixed_output None = Some (Znth index sorted 0)).

(** Sequential copy-back state: exactly the target prefix has been written,
    and the untouched suffix still comes from the original input. *)
Definition CountingCopyProgress
    (before target live : list Z) (copied : Z) : Prop :=
  live =
    app
      (sublist 0 copied target)
      (sublist copied (Zlength before) before).
