Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MSISStrictlyIncreasingValues (l idxs : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength idxs ->
    Znth (Znth p idxs 0) l 0 < Znth (Znth q idxs 0) l 0.

Definition MSISValidSubsequence
    (l : list Z) (limit : Z) (idxs : list Z) : Prop :=
  0 <= limit <= Zlength l /\
  0 < Zlength idxs /\
  Forall (fun idx => 0 <= idx < limit) idxs /\
  mono_inc idxs /\
  MSISStrictlyIncreasingValues l idxs.

Definition MSISSubsequenceSum (l idxs : list Z) : Z :=
  sum (map (fun idx => Znth idx l 0) idxs).

Definition MSISPrefix (l : list Z) (limit ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => MSISValidSubsequence l limit idxs)
    (fun idxs => MSISSubsequenceSum l idxs)
    ans.

Definition MSISMaximum (l : list Z) (ans : Z) : Prop :=
  MSISPrefix l (Zlength l) ans.
