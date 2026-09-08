Require Import PVbench.Algorithms.max_sum_increasing_sequence.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MSISInnerCandidate
    (l dp : list Z) (i scanned candidate : Z) : Prop :=
  candidate = Znth i l 0 \/
  exists k,
    0 <= k < scanned /\
    Znth k l 0 < Znth i l 0 /\
    candidate = Znth k dp 0 + Znth i l 0.
Definition MSISInnerProgress
    (l dp : list Z) (i scanned : Z) : Prop :=
  1 <= i < Zlength l /\
  0 <= scanned <= i /\
  Zlength dp = i + 1 /\
  (forall k,
    0 <= k < i ->
    MSISEndingAt l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= (k + 1) * 10000) /\
  max_value_of_subset Z.le
    (fun candidate => MSISInnerCandidate l dp i scanned candidate)
    (fun candidate => candidate)
    (Znth i dp 0) /\
  1 <= Znth i dp 0 <= (i + 1) * 10000.
Definition MSISBestSoFar (l : list Z) (limit ans : Z) : Prop :=
  1 <= limit <= Zlength l /\
  MSISPrefix l limit ans.
