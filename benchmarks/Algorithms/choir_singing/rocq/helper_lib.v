Require Import PVbench.Algorithms.choir_singing.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ChoirOnesPrefix (values : list Z) (written : Z) : Prop :=
  Zlength values = written /\
  forall k, 0 <= k < written -> Znth k values 0 = 1.
Definition ChoirOnesFull (values : list Z) (n : Z) : Prop :=
  Zlength values = n /\
  forall k, 0 <= k < n -> Znth k values 0 = 1.
Definition ChoirLeftCandidate
    (heights dp_left : list Z)
    (peak scanned candidate : Z) : Prop :=
  candidate = 1 \/
  exists k,
    scanned <= k < peak /\
    Znth k heights 0 < Znth peak heights 0 /\
    candidate = Znth k dp_left 0 + 1.
Definition ChoirLeftInnerProgress
    (heights dp_left : list Z) (peak scanned : Z) : Prop :=
  0 <= peak < Zlength heights /\
  0 <= scanned <= peak /\
  Zlength dp_left = Zlength heights /\
  (forall k,
      0 <= k < peak ->
      ChoirLeftLength heights k (Znth k dp_left 0) /\
      1 <= Znth k dp_left 0 <= k + 1) /\
  (forall k,
      peak < k < Zlength heights ->
      Znth k dp_left 0 = 1) /\
  max_value_of_subset Z.le
    (fun candidate =>
       ChoirLeftCandidate heights dp_left peak scanned candidate)
    (fun candidate => candidate)
    (Znth peak dp_left 0) /\
  1 <= Znth peak dp_left 0 <= peak + 1.
Definition ChoirRightCandidate
    (heights dp_right : list Z)
    (peak scanned candidate : Z) : Prop :=
  candidate = 1 \/
  exists k,
    peak < k < scanned /\
    Znth k heights 0 < Znth peak heights 0 /\
    candidate = Znth k dp_right 0 + 1.
Definition ChoirRightInnerProgress
    (heights dp_right : list Z) (peak scanned : Z) : Prop :=
  0 <= peak < Zlength heights /\
  peak + 1 <= scanned <= Zlength heights /\
  Zlength dp_right = Zlength heights /\
  (forall k,
      peak < k < Zlength heights ->
      ChoirRightLength heights k (Znth k dp_right 0) /\
      1 <= Znth k dp_right 0 <= Zlength heights - k) /\
  (forall k,
      0 <= k < peak ->
      Znth k dp_right 0 = 1) /\
  max_value_of_subset Z.le
    (fun candidate =>
       ChoirRightCandidate heights dp_right peak scanned candidate)
    (fun candidate => candidate)
    (Znth peak dp_right 0) /\
  1 <= Znth peak dp_right 0 <= Zlength heights - peak.
