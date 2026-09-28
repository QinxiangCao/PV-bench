Require Export PVbench.Algorithms.kings_game.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Lia.

Definition minister_product (p : minister) : Z :=
  minister_left p * minister_right p.

(** The greedy key and its mathematical sortedness property. *)
Definition MinisterProductLe (p q : minister) : Prop :=
  minister_product p <= minister_product q.

(** Exact mathematical effects of swapping two flat minister records. *)
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

(** Pure ordering progress; list-length bindings and scan ranges stay in C. *)
Definition BubbleOuterProperty (ps : list minister) (n pass : Z) : Prop :=
  (forall i j, n - pass <= i -> i <= j -> j < n ->
    MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister)) /\
  (forall i j, 0 <= i -> i < n - pass -> n - pass <= j -> j < n ->
    MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister)).

Definition BubbleScanProperty (ps : list minister) (n pass j : Z) : Prop :=
  max_value_of_subset Z.le (fun k : Z => 0 <= k <= j)
    (fun k => minister_product (Znth k ps default_minister))
    (minister_product (Znth j ps default_minister)).
