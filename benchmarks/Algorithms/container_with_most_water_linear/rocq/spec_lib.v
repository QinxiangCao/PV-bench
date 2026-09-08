Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition LinearContainerHeight (l : list Z) (i j : Z) : Z :=
  Z.min (Znth i l 0) (Znth j l 0).
Definition LinearContainerArea (l : list Z) (i j : Z) : Z :=
  (j - i) * LinearContainerHeight l i j.
Definition LinearContainerPair (l : list Z) (i j : Z) : Prop :=
  0 <= i /\ i < j /\ j < Zlength l.

(** The exact, implementation-independent optimization problem: [ans] is
    attained by a valid pair and dominates every valid pair. *)
Definition MaximumContainerArea (l : list Z) (ans : Z) : Prop :=
  (exists i j,
      LinearContainerPair l i j /\
      ans = LinearContainerArea l i j) /\
  forall i j,
    LinearContainerPair l i j ->
    LinearContainerArea l i j <= ans.

(** [best] is either the initial zero or the area of an inspected pair. *)
