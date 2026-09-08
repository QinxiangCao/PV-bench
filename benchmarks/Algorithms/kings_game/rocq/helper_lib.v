Require Import PVbench.Algorithms.kings_game.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition minister_swap
    (ps : list minister) (i j : Z) : list minister :=
  replace_Znth j (Znth i ps default_minister)
    (replace_Znth i (Znth j ps default_minister) ps).
Definition minister_swap_flat
    (flat : list Z) (i j : Z) : list Z :=
  let il := Znth (2 * i) flat 0 in
  let ir := Znth (2 * i + 1) flat 0 in
  let jl := Znth (2 * j) flat 0 in
  let jr := Znth (2 * j + 1) flat 0 in
  replace_Znth (2 * j + 1) ir
    (replace_Znth (2 * j) il
      (replace_Znth (2 * i + 1) jr
        (replace_Znth (2 * i) jl flat))).

(** Predicate-first bubble-sort invariants.  [BubbleOuterProperty] says that
    the last [pass] records are sorted and dominate the remaining prefix.
    [BubbleScanProperty] says that position [j] contains a maximum greedy key
    of the scanned prefix. *)
Definition BubbleOuterProperty
    (ps : list minister) (n pass : Z) : Prop :=
  Zlength ps = n /\
  (forall i j,
      n - pass <= i -> i <= j -> j < n ->
      MinisterProductLe
        (Znth i ps default_minister)
        (Znth j ps default_minister)) /\
  (forall i j,
      0 <= i -> i < n - pass ->
      n - pass <= j -> j < n ->
      MinisterProductLe
        (Znth i ps default_minister)
        (Znth j ps default_minister)).
Definition BubbleScanProperty
    (ps : list minister) (n pass j : Z) : Prop :=
  0 <= j < n - pass /\
  forall k,
    0 <= k -> k <= j ->
    MinisterProductLe
      (Znth k ps default_minister)
      (Znth j ps default_minister).

Require Import Coq.micromega.Lia.
