Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.Sorting.Sorted.

(** A mathematical interval record.  The C representation is deliberately
    kept separate: its two fields live in the disjoint [st] and [ed] arrays. *)
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
  Forall2 (fun start p => start = interval_start p) starts ps /\
  Forall2 (fun finish p => finish = interval_end p) ends ps.

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
