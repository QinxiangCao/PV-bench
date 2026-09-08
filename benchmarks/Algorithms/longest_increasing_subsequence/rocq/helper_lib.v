Require Import PVbench.Algorithms.longest_increasing_subsequence.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition LISDPInnerCandidate
    (l dp : list Z) (i scanned candidate : Z) : Prop :=
  candidate = 1 \/
  exists k,
    0 <= k < scanned /\
    Znth k l 0 < Znth i l 0 /\
    candidate = Znth k dp 0 + 1.
Definition LISInnerProgress
    (l dp : list Z) (i scanned : Z) : Prop :=
  0 <= i < Zlength l /\
  0 <= scanned <= i /\
  Zlength dp = i + 1 /\
  (forall k,
    0 <= k < i ->
    LISEndingAtLength l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= k + 1) /\
  max_value_of_subset Z.le
    (fun candidate => LISDPInnerCandidate l dp i scanned candidate)
    (fun candidate => candidate)
    (Znth i dp 0) /\
  1 <= Znth i dp 0 <= i + 1.
Definition LISBestSoFar (l : list Z) (limit ans : Z) : Prop :=
  0 <= limit <= Zlength l /\
  ((limit = 0 /\ ans = 1) \/
   (0 < limit /\ LISPrefix l limit ans)).

Require Import Coq.micromega.Lia.
