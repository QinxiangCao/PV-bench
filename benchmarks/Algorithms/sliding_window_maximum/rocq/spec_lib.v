Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
Require Import MaxMinLib.MaxMin.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** Functional and algorithmic layer. *)

Definition WindowMaxValue (l : list Z) (lo hi ans : Z) : Prop :=
  max_value_of_subset Z.le (fun pos : Z => lo <= pos < hi)
    (fun pos => Znth pos l 0) ans.

Definition SlidingWindowMaximum (l : list Z) (k : Z) (out : list Z) : Prop :=
  Zlength out = Zlength l - k + 1 /\
  forall idx,
    0 <= idx < Zlength out ->
    WindowMaxValue l idx (idx + k) (Znth idx out 0).
