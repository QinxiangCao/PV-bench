Require Export PVbench.Algorithms.choir_singing.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ChoirLeftLength
    (heights : list Z) (peak answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun indices => ChoirValidIncreasingEndingAt heights peak indices)
    (fun indices => Zlength indices)
    answer.

Definition ChoirRightLength
    (heights : list Z) (peak answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun indices => ChoirValidDecreasingStartingAt heights peak indices)
    (fun indices => Zlength indices)
    answer.

(* Progress predicates contain only the mathematical table contents.
   Cursor bounds and array ownership belong to the C annotations. *)
Definition ChoirDPLeftPrefix
    (heights dp_left : list Z) (hi : Z) : Prop :=
  (forall k, 0 <= k < hi ->
    ChoirLeftLength heights k (Znth k dp_left 0)) /\
  Forall (eq 1) (sublist hi (Zlength heights) dp_left).

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
  (forall k, 0 <= k < peak ->
    ChoirLeftLength heights k (Znth k dp_left 0)) /\
  Forall (eq 1) (sublist (peak + 1) (Zlength heights) dp_left) /\
  max_value_of_subset Z.le
    (ChoirLeftCandidate heights dp_left peak scanned)
    (fun candidate => candidate) (Znth peak dp_left 0).

Definition ChoirDPRightSuffix
    (heights dp_right : list Z) (lo : Z) : Prop :=
  (forall k, lo <= k < Zlength heights ->
    ChoirRightLength heights k (Znth k dp_right 0)) /\
  Forall (eq 1) (sublist 0 lo dp_right).

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
  (forall k, peak < k < Zlength heights ->
    ChoirRightLength heights k (Znth k dp_right 0)) /\
  Forall (eq 1) (sublist 0 peak dp_right) /\
  max_value_of_subset Z.le
    (ChoirRightCandidate heights dp_right peak scanned)
    (fun candidate => candidate) (Znth peak dp_right 0).

Definition ChoirPeakLength
    (heights : list Z) (peak answer : Z) : Prop :=
  exists left right,
    ChoirLeftLength heights peak left /\
    ChoirRightLength heights peak right /\
    answer = left + right - 1.

Definition ChoirBestPrefix
    (heights : list Z) (limit answer : Z) : Prop :=
  ((limit = 0 /\ answer = 0) \/
   (0 < limit /\
    max_value_of_subset Z.le
      (fun candidate =>
         exists peak,
           0 <= peak < limit /\
           ChoirPeakLength heights peak candidate)
      (fun candidate => candidate)
      answer)).
