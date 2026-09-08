Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StrictlyIncreasingValues (l idxs : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength idxs ->
    Znth (Znth p idxs 0) l 0 < Znth (Znth q idxs 0) l 0.
Definition ValidIncreasingSubsequence
    (l : list Z) (limit : Z) (idxs : list Z) : Prop :=
  0 <= limit <= Zlength l /\
  Forall (fun idx => 0 <= idx < limit) idxs /\
  mono_inc idxs /\
  StrictlyIncreasingValues l idxs.
Definition ValidIncreasingSubsequenceEndingAt
    (l : list Z) (i : Z) (idxs : list Z) : Prop :=
  0 <= i < Zlength l /\
  ValidIncreasingSubsequence l (i + 1) idxs /\
  exists prefix, idxs = prefix ++ i :: nil.
Definition LISPrefix (l : list Z) (limit ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidIncreasingSubsequence l limit idxs)
    (fun idxs => Zlength idxs)
    ans.
Definition LISLength (l : list Z) (ans : Z) : Prop :=
  LISPrefix l (Zlength l) ans.
Definition LISEndingAtLength (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidIncreasingSubsequenceEndingAt l i idxs)
    (fun idxs => Zlength idxs)
    ans.
Definition LISDPTablePrefix
    (l dp : list Z) (hi : Z) : Prop :=
  0 <= hi <= Zlength l /\
  Zlength dp = hi /\
  forall k,
    0 <= k < hi ->
    LISEndingAtLength l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= k + 1.
