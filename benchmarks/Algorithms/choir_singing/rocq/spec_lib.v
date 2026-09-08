Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ChoirStrictlyIncreasingValues
    (heights indices : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength indices ->
    Znth (Znth p indices 0) heights 0 <
    Znth (Znth q indices 0) heights 0.
Definition ChoirStrictlyDecreasingValues
    (heights indices : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength indices ->
    Znth (Znth q indices 0) heights 0 <
    Znth (Znth p indices 0) heights 0.
Definition ChoirValidIncreasingEndingAt
    (heights : list Z) (peak : Z) (indices : list Z) : Prop :=
  0 <= peak < Zlength heights /\
  Forall (fun idx => 0 <= idx <= peak) indices /\
  mono_inc indices /\
  ChoirStrictlyIncreasingValues heights indices /\
  exists prefix, indices = prefix ++ peak :: nil.
Definition ChoirValidDecreasingStartingAt
    (heights : list Z) (peak : Z) (indices : list Z) : Prop :=
  0 <= peak < Zlength heights /\
  Forall (fun idx => peak <= idx < Zlength heights) indices /\
  mono_inc indices /\
  ChoirStrictlyDecreasingValues heights indices /\
  exists suffix, indices = peak :: suffix.
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
Definition ChoirDPLeftPrefix
    (heights dp_left : list Z) (hi : Z) : Prop :=
  0 <= hi <= Zlength heights /\
  Zlength dp_left = Zlength heights /\
  (forall k,
      0 <= k < hi ->
      ChoirLeftLength heights k (Znth k dp_left 0) /\
      1 <= Znth k dp_left 0 <= k + 1) /\
  (forall k,
      hi <= k < Zlength heights ->
      Znth k dp_left 0 = 1).
Definition ChoirDPRightSuffix
    (heights dp_right : list Z) (lo : Z) : Prop :=
  0 <= lo <= Zlength heights /\
  Zlength dp_right = Zlength heights /\
  (forall k,
      lo <= k < Zlength heights ->
      ChoirRightLength heights k (Znth k dp_right 0) /\
      1 <= Znth k dp_right 0 <= Zlength heights - k) /\
  (forall k,
      0 <= k < lo ->
      Znth k dp_right 0 = 1).
Definition ChoirPeakLength
    (heights : list Z) (peak answer : Z) : Prop :=
  exists left right,
    ChoirLeftLength heights peak left /\
    ChoirRightLength heights peak right /\
    answer = left + right - 1.
Definition ChoirBestPrefix
    (heights : list Z) (limit answer : Z) : Prop :=
  0 <= limit <= Zlength heights /\
  ((limit = 0 /\ answer = 0) \/
   (0 < limit /\
    max_value_of_subset Z.le
      (fun candidate =>
         exists peak,
           0 <= peak < limit /\
           ChoirPeakLength heights peak candidate)
      (fun candidate => candidate)
      answer)).
Definition ChoirLength (heights : list Z) (answer : Z) : Prop :=
  ChoirBestPrefix heights (Zlength heights) answer.
Definition ChoirMinimumRemovals
    (heights : list Z) (removed : Z) : Prop :=
  exists best,
    ChoirLength heights best /\
    removed = Zlength heights - best.
