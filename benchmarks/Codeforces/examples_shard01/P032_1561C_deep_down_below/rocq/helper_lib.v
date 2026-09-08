Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import ListLib.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P032_1561C_deep_down_below.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* The two implementation arrays are one mathematical sequence of cave
   summaries.  Keeping the permutation on [combine] records that every swap
   moves a requirement together with its corresponding gain. *)
Definition ParallelPermutation
    (requirements gains requirements' gains' : list Z) : Prop :=
  Permutation (combine requirements gains) (combine requirements' gains').

Definition HeapParentsFrom (requirements : list Z) (lo hi : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    Znth child requirements 0 <=
    Znth ((child - 1) / 2) requirements 0.

(* During sift-down every heap edge in the relevant suffix is ordered except
   possibly the two edges leaving the current hole. *)
Definition HeapOrderedExceptAtFrom
    (requirements : list Z) (lo hi bad : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    (child - 1) / 2 <> bad ->
    Znth child requirements 0 <=
    Znth ((child - 1) / 2) requirements 0.

Definition SelectedLargerChild
    (requirements : list Z) (root hi child : Z) : Prop :=
  (child = 2 * root + 1 \/ child = 2 * root + 2) /\
  child <= hi /\
  (2 * root + 1 <= hi ->
     Znth (2 * root + 1) requirements 0 <= Znth child requirements 0) /\
  (2 * root + 2 <= hi ->
     Znth (2 * root + 2) requirements 0 <= Znth child requirements 0).

Definition HeapSortState
    (requirements0 gains0 requirements gains : list Z) (hi : Z) : Prop :=
  Zlength requirements = Zlength requirements0 /\
  Zlength gains = Zlength gains0 /\
  ParallelPermutation requirements0 gains0 requirements gains /\
  HeapParentsFrom requirements 0 hi /\
  ListLib.increasing
    (sublist (hi + 1) (Zlength requirements) requirements) /\
  (forall p q,
     0 <= p <= hi ->
     hi < q < Zlength requirements ->
     Znth p requirements 0 <= Znth q requirements 0).

Definition GreedyNeed
    (requirements gains : list Z) (done need : Z) : Prop :=
  0 <= need /\
  (forall k, 0 <= k < done ->
     Znth k requirements 0 - ListLib.sum (sublist 0 k gains) <= need) /\
  (need = 0 \/
   exists k, 0 <= k < done /\
     need = Znth k requirements 0 - ListLib.sum (sublist 0 k gains)).

Definition SortedCaveSummaries
    (caves : list (list Z))
    (requirements0 gains0 requirements gains : list Z) : Prop :=
  CaveSummaryBridge caves requirements0 gains0 /\
  ParallelPermutation requirements0 gains0 requirements gains /\
  ListLib.increasing requirements.

Definition CaveInputBounds (caves : list (list Z)) : Prop :=
  1 <= Zlength caves <= 100000 /\
  (forall i, 0 <= i < Zlength caves ->
     0 < Zlength (Znth i caves []) <= 100000) /\
  Zlength (concat caves) <= 100000 /\
  (forall k, 0 <= k < Zlength (concat caves) ->
     1 <= Znth k (concat caves) 0 <= 1000000000).

Definition CaveSummaryBounds (requirements gains : list Z) : Prop :=
  Zlength requirements = Zlength gains /\
  0 <= ListLib.sum gains <= 100000 /\
  (forall i, 0 <= i < Zlength requirements ->
     1 <= Znth i requirements 0 <= 1000000001 /\
     1 <= Znth i gains 0 <= 100000).
