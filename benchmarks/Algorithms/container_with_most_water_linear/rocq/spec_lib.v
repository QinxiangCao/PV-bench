Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Require Import MaxMinLib.MaxMin.
Import ListNotations.
Local Open Scope Z_scope.

(** Mathematical area of the container whose endpoints are [i] and [j]. *)
Definition LinearContainerHeight (l : list Z) (i j : Z) : Z :=
  Z.min (Znth i l 0) (Znth j l 0).

Definition LinearContainerArea (l : list Z) (i j : Z) : Z :=
  (j - i) * LinearContainerHeight l i j.

Definition LinearContainerPair (l : list Z) (i j : Z) : Prop :=
  0 <= i /\ i < j /\ j < Zlength l.

(** The exact, implementation-independent optimization problem: [ans] is
    attained by a valid pair and dominates every valid pair. *)
Definition MaximumContainerArea (l : list Z) (ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun ij : Z * Z => LinearContainerPair l (fst ij) (snd ij))
    (fun ij => LinearContainerArea l (fst ij) (snd ij)) ans.
