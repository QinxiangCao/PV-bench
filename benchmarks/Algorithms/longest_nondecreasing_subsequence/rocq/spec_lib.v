Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Psatz.

Definition NondecreasingValues (l idxs : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength idxs ->
    Znth (Znth p idxs 0) l 0 <= Znth (Znth q idxs 0) l 0.

Definition ValidNondecreasingSubsequence
    (l : list Z) (limit : Z) (idxs : list Z) : Prop :=
  0 <= limit <= Zlength l /\
  Forall (fun idx => 0 <= idx < limit) idxs /\
  mono_inc idxs /\
  NondecreasingValues l idxs.

Definition LNDSLengthPrefix (l : list Z) (limit ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidNondecreasingSubsequence l limit idxs)
    (fun idxs => Zlength idxs)
    ans.

Definition LNDSLength (l : list Z) (ans : Z) : Prop :=
  LNDSLengthPrefix l (Zlength l) ans.
