Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Require Import SumLib.ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

(** Implementation-independent semantics of one legal container. *)
Definition ContainerHeightNLogN (l : list Z) (i j : Z) : Z :=
  Z.min (Znth i l 0) (Znth j l 0).

Definition ContainerAreaNLogN (l : list Z) (i j : Z) : Z :=
  (j - i) * ContainerHeightNLogN l i j.

Definition ContainerPairNLogN (l : list Z) (i j : Z) : Prop :=
  0 <= i /\ i < j /\ j < Zlength l.

(** The exact attained global optimum, stated only in terms of original
    indices.  A different implementation can satisfy the same predicate. *)
Definition MaximumContainerArea (l : list Z) (ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun ij : Z * Z => ContainerPairNLogN l (fst ij) (snd ij))
    (fun ij => ContainerAreaNLogN l (fst ij) (snd ij)) ans.
