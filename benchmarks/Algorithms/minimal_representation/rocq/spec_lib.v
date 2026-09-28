From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Require Import MaxMinLib.MaxMin.
From Coq Require Import Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
From Coq Require Import Lia.

(** The mathematical rotation is the length-[l] segment beginning at [start]
    in the doubled input.  It is independent of the candidate-elimination
    implementation used by the C function. *)
Definition MRRotation (l : list Z) (start : Z) : list Z :=
  sublist start (start + Zlength l) (l ++ l).

Definition MRValidStart (l : list Z) (start : Z) : Prop :=
  0 <= start < Zlength l.

Definition MRRotationValue
    (l : list Z) (start offset : Z) : Z :=
  Znth (start + offset) (l ++ l) 0.

Definition MRRotationPrefixEq
    (l : list Z) (left right prefix_len : Z) : Prop :=
  forall offset,
    0 <= offset < prefix_len ->
    MRRotationValue l left offset = MRRotationValue l right offset.

Definition MRRotationEq (l : list Z) (left right : Z) : Prop :=
  MRRotationPrefixEq l left right (Zlength l).

Definition MRRotationLt (l : list Z) (left right : Z) : Prop :=
  exists first_diff,
    0 <= first_diff < Zlength l /\
    MRRotationPrefixEq l left right first_diff /\
    MRRotationValue l left first_diff <
      MRRotationValue l right first_diff.

Definition MRRotationLe (l : list Z) (left right : Z) : Prop :=
  MRRotationLt l left right \/ MRRotationEq l left right.

(** [start] denotes a globally lexicographically minimal rotation. *)
Definition MRMinimalRotationAt (l : list Z) (start : Z) : Prop :=
  min_value_of_subset (MRRotationLe l) (MRValidStart l)
    (fun pos : Z => pos) start.

(** Both the lexicographic optimum and its tie-breaking index use MinMax. *)
Definition MRFirstMinimalRotationAt (l : list Z) (start : Z) : Prop :=
  MRMinimalRotationAt l start /\
  min_value_of_subset Z.le
    (fun other => MRValidStart l other /\ MRRotationEq l start other)
    (fun pos : Z => pos) start.
