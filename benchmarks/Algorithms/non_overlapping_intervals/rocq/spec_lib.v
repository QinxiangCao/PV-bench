Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition interval : Type := (Z * Z)%type.
Definition mk_interval (start finish : Z) : interval := (start, finish).
Definition interval_start (p : interval) : Z := fst p.
Definition interval_end (p : interval) : Z := snd p.
Definition default_interval : interval := mk_interval 0 1.

(** [PairIntervals starts ends ps] says that the two parallel logical arrays
    encode exactly the complete interval records in [ps], at the same indices.
    In particular, no specification is phrased through a flat array. *)
Definition PairIntervals
    (starts ends : list Z) (ps : list interval) : Prop :=
  Zlength starts = Zlength ends /\
  Zlength ps = Zlength starts /\
  forall k,
    0 <= k < Zlength starts ->
    Znth k ps default_interval =
      mk_interval (Znth k starts 0) (Znth k ends 0).
Definition IntervalBounds (ps : list interval) : Prop :=
  Forall
    (fun p =>
       -10000 <= interval_start p /\
       interval_start p < interval_end p /\
       interval_end p <= 10000)
    ps.
Definition IntervalPermutation : list interval -> list interval -> Prop :=
  @Permutation interval.

(** Exact record-level swap used by both parallel arrays. *)
Definition IntervalsEndSorted (ps : list interval) : Prop :=
  forall i j,
    0 <= i -> i <= j -> j < Zlength ps ->
    interval_end (Znth i ps default_interval) <=
    interval_end (Znth j ps default_interval).

(** A retained schedule is ordered from left to right and therefore contains
    no overlapping pair.  Touching endpoints are explicitly permitted. *)
Definition NonOverlappingSchedule (kept : list interval) : Prop :=
  forall i j,
    0 <= i -> i < j -> j < Zlength kept ->
    interval_end (Znth i kept default_interval) <=
    interval_start (Znth j kept default_interval).

(** [kept] selects complete interval records from [input], with multiplicity. *)
Definition IntervalSelection
    (input kept : list interval) : Prop :=
  exists removed,
    Permutation input (kept ++ removed).
Definition FeasibleRemovalCount
    (input : list interval) (removed_count : Z) : Prop :=
  exists kept,
    IntervalSelection input kept /\
    NonOverlappingSchedule kept /\
    removed_count = Zlength input - Zlength kept.

(** The required optimum is stated directly through the repository MinMax
    library: [answer] is the minimum of all feasible removal counts. *)
Definition MinimumRemovals
    (input : list interval) (answer : Z) : Prop :=
  min_value_of_subset Z.le
    (FeasibleRemovalCount input)
    (fun removed_count => removed_count)
    answer.

(** Predicate-first Lomuto scan state.  Machine index ranges, parallel-array
    ownership, record bounds, and array-read bindings stay in C annotations. *)
