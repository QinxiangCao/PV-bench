From Coq Require Import ZArith List.
From AUXLib Require Import ListLib MonotonicList.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Lia Ring.
From Coq Require Import Lia.
From Coq Require Import micromega.Psatz.
From MaxMinLib Require Import MaxMin Interface.
From Coq Require Import Sorting.Sorted.

(** A common subsequence is a sequence of matching positions, strictly
    increasing in both inputs. These are mathematical candidate domains. *)
Definition LCSNPositionOrder (p q : Z * Z) : Prop :=
  fst p < fst q /\ snd p < snd q.

Definition LCSNMatching (xs ys : list Z) (rows cols : Z)
    (pairs : list (Z * Z)) : Prop :=
  Forall (fun p => 0 <= fst p < rows /\ 0 <= snd p < cols /\
    Znth (fst p) xs 0 = Znth (snd p) ys 0) pairs /\
  StronglySorted LCSNPositionOrder pairs.

Definition LCSNLength (xs ys : list Z) (answer : Z) : Prop :=
  max_value_of_subset Z.le
    (LCSNMatching xs ys (Zlength xs) (Zlength ys)) (fun pairs => Zlength pairs) answer.
