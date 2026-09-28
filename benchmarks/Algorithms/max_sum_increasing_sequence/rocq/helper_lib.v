Require Export PVbench.Algorithms.max_sum_increasing_sequence.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MSISValidSubsequenceEndingAt
    (l : list Z) (i : Z) (idxs : list Z) : Prop :=
  0 <= i < Zlength l /\
  MSISValidSubsequence l (i + 1) idxs /\
  exists prefix, idxs = prefix ++ i :: nil.

Definition MSISEndingAt (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => MSISValidSubsequenceEndingAt l i idxs)
    (fun idxs => MSISSubsequenceSum l idxs)
    ans.

Definition MSISInnerCandidate
    (l dp : list Z) (i scanned candidate : Z) : Prop :=
  candidate = Znth i l 0 \/
  exists k,
    0 <= k < scanned /\
    Znth k l 0 < Znth i l 0 /\
    candidate = Znth k dp 0 + Znth i l 0.

(** Public mathematical predicates exclude input limits, workspace shape,
    and bounds needed only by the implementation. *)
Definition MSISDPTablePrefix (l dp : list Z) (hi : Z) : Prop :=
  forall k, 0 <= k < hi -> MSISEndingAt l k (Znth k dp 0).

Definition MSISInnerProgress (l dp : list Z) (i scanned : Z) : Prop :=
  MSISDPTablePrefix l dp i /\
  max_value_of_subset Z.le
    (fun candidate => MSISInnerCandidate l dp i scanned candidate)
    (fun candidate => candidate) (Znth i dp 0).

Definition MSISBestSoFar (l : list Z) (limit ans : Z) : Prop :=
  MSISPrefix l limit ans.
