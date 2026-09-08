Require Import PVbench.Algorithms.container_with_most_water_linear.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition LinearContainerBest (l : list Z) (best : Z) : Prop :=
  best = 0 \/
  exists i j,
    LinearContainerPair l i j /\ best = LinearContainerArea l i j.
Definition LinearContainerRemaining
    (l : list Z) (left right i j : Z) : Prop :=
  LinearContainerPair l i j /\ left <= i /\ j <= right.

(** Every pair discarded by the two-pointer search is already dominated by
    [best], or by a pair that remains in the current closed interval.  This is
    a semantic frontier property, independent of the program's control flow. *)
Definition LinearContainerTwoPointerInvariant
    (l : list Z) (left right best : Z) : Prop :=
  LinearContainerBest l best /\
  forall i j,
    LinearContainerPair l i j ->
    LinearContainerArea l i j <= best \/
    exists p q,
      LinearContainerRemaining l left right p q /\
      LinearContainerArea l i j <= LinearContainerArea l p q.
