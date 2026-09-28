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

(* A formation is represented by its increasing and decreasing arms.
   Both contain the same peak, which is counted only once in the cost. *)
Definition ChoirMinimumRemovals (heights : list Z) (removed : Z) : Prop :=
  min_value_of_subset Z.le
    (fun arms : list Z * list Z =>
      exists peak,
        ChoirValidIncreasingEndingAt heights peak (fst arms) /\
        ChoirValidDecreasingStartingAt heights peak (snd arms))
    (fun arms => Zlength heights -
      (Zlength (fst arms) + Zlength (snd arms) - 1)) removed.
