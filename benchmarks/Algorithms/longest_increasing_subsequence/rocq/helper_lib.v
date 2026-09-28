Require Export PVbench.Algorithms.longest_increasing_subsequence.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Lia.

Definition ValidIncreasingSubsequenceEndingAt
    (l : list Z) (i : Z) (idxs : list Z) : Prop :=
  0 <= i < Zlength l /\
  ValidIncreasingSubsequence l (i + 1) idxs /\
  exists prefix, idxs = prefix ++ i :: nil.

Definition LISEndingAtLength (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidIncreasingSubsequenceEndingAt l i idxs)
    (fun idxs => Zlength idxs)
    ans.

Definition LISDPInnerCandidate
    (l dp : list Z) (i scanned candidate : Z) : Prop :=
  candidate = 1 \/
  exists k,
    0 <= k < scanned /\
    Znth k l 0 < Znth i l 0 /\
    candidate = Znth k dp 0 + 1.

(** Mathematical progress is separate from the workspace shape and bounds.
    The established helper lemmas above retain their facts records for reuse. *)
Definition LISDPTablePrefix (l dp : list Z) (hi : Z) : Prop :=
  forall k, 0 <= k < hi -> LISEndingAtLength l k (Znth k dp 0).

Definition LISInnerProgress (l dp : list Z) (i scanned : Z) : Prop :=
  LISDPTablePrefix l dp i /\
  max_value_of_subset Z.le
    (fun candidate => LISDPInnerCandidate l dp i scanned candidate)
    (fun candidate => candidate) (Znth i dp 0).

Definition LISBestSoFar (l : list Z) (limit ans : Z) : Prop :=
  (limit = 0 /\ ans = 1) \/ (0 < limit /\ LISPrefix l limit ans).
