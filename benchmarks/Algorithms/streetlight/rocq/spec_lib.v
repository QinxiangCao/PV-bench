From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

From Coq Require Import Lia.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.

Require Import Coq.Relations.Relation_Operators.
Require Import AUXLib.MonotonicList.

From SumLib Require Import ZRange.
Require Import Coq.Sorting.Permutation.
Local Notation sum := AUXLib.ListLib.sum.

(** General itineraries specify the light switched off at each stop and the
    time spent reaching it.  They permit every order and extra travel time;
    lights passed along the way need not be switched off immediately. *)
Definition StreetlightTravelAllowed (positions : list Z) (start : Z)
    (moves : list (Z * Z)) : Prop :=
  Forall (fun leg =>
    Z.abs (Znth (fst leg) positions 0 - Znth (fst (snd leg)) positions 0) <= snd (snd leg))
    (combine (start :: map (@fst Z Z) moves) moves).

Definition StreetlightWalkStep (powers : list Z)
    (state : Z * Z * Z) (move : Z * Z) : Z * Z * Z :=
  let '(current, remaining, energy) := state in
  (fst move, remaining - Znth (fst move) powers 0, energy + snd move * remaining).

Definition StreetlightTourEnergy (powers : list Z) (start : Z)
    (moves : list (Z * Z)) : Z :=
  snd (fold_left (StreetlightWalkStep powers) moves
    (start, sum powers - Znth start powers 0, 0)).

Definition StreetlightTourMinimumEnergy (positions powers : list Z)
    (start answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun moves =>
      Permutation (Zrange 0 start ++ Zrange (start + 1) (Zlength positions))
        (map (@fst Z Z) moves) /\ StreetlightTravelAllowed positions start moves)
    (StreetlightTourEnergy powers start) answer.
