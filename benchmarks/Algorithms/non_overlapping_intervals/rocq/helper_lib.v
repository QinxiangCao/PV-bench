Require Import PVbench.Algorithms.non_overlapping_intervals.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition interval_swap
    (ps : list interval) (i j : Z) : list interval :=
  replace_Znth j (Znth i ps default_interval)
    (replace_Znth i (Znth j ps default_interval) ps).
Definition IntervalSwappedAt
    (before after : list interval) (i j : Z) : Prop :=
  after = interval_swap before i j.

(** Quicksort changes only the requested complete-record range. *)
Definition IntervalSameOutsideRange
    (before after : list interval) (left right : Z) : Prop :=
  Zlength before = Zlength after /\
  forall k,
    0 <= k < Zlength before ->
    (k < left \/ right < k) ->
    Znth k after default_interval = Znth k before default_interval.

(** Lomuto partition places its pivot record between a non-strict left
    partition and a strict right partition, ordered by interval end. *)
Definition IntervalPartitionedAt
    (ps : list interval) (low high pivot : Z) : Prop :=
  low <= pivot <= high /\
  (forall k,
      low <= k < pivot ->
      interval_end (Znth k ps default_interval) <=
      interval_end (Znth pivot ps default_interval)) /\
  (forall k,
      pivot < k <= high ->
      interval_end (Znth pivot ps default_interval) <
      interval_end (Znth k ps default_interval)).
Definition IntervalsEndSortedRange
    (ps : list interval) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    interval_end (Znth i ps default_interval) <=
    interval_end (Znth j ps default_interval).
Definition LomutoScanState
    (before current : list interval)
    (low high placed scanned pivot_end : Z) : Prop :=
  IntervalPermutation before current /\
  IntervalSameOutsideRange before current low high /\
  interval_end (Znth high current default_interval) = pivot_end /\
  (forall k,
      low <= k <= placed ->
      interval_end (Znth k current default_interval) <= pivot_end) /\
  (forall k,
      placed < k < scanned ->
      pivot_end < interval_end (Znth k current default_interval)).
Definition schedule_finish (kept : list interval) : Z :=
  interval_end
    (Znth (Zlength kept - 1) kept default_interval).

(** On a finish-sorted prefix, the greedy schedule has maximum cardinality;
    among schedules of that cardinality it has the smallest last finish. *)
Definition GreedyPrefixState
    (ps : list interval) (processed kept_count last_finish : Z) : Prop :=
  exists kept,
    IntervalSelection (sublist 0 processed ps) kept /\
    NonOverlappingSchedule kept /\
    Zlength kept = kept_count /\
    0 < Zlength kept /\
    last_finish = schedule_finish kept /\
    (forall alternative,
        IntervalSelection (sublist 0 processed ps) alternative ->
        NonOverlappingSchedule alternative ->
        Zlength alternative <= kept_count) /\
    (forall alternative,
        IntervalSelection (sublist 0 processed ps) alternative ->
        NonOverlappingSchedule alternative ->
        Zlength alternative = kept_count ->
        last_finish <= schedule_finish alternative).
