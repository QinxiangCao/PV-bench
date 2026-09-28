Require Export PVbench.Algorithms.optimized_selection_sort.rocq.spec_lib.
(* Shared minimum predicate for both selection-sort implementations. *)
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib MonotonicList.
Require Import MaxMinLib.MaxMin.
Local Open Scope Z_scope.

(** Minimum value of the mathematical candidate segment. *)
Definition selection_minimum (values : list Z) (value : Z) : Prop :=
  min_value_of_subset Z.le (fun x => In x values) (fun x : Z => x) value.

From Coq Require Import ZArith List Sorting.Permutation.
From AUXLib Require Import ListLib.
