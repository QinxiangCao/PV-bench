From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

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
  MRValidStart l start /\
  forall other,
    MRValidStart l other ->
    MRRotationLe l start other.

(** Ties between identical rotations are resolved by the smallest start. *)
Definition MRFirstMinimalRotationAt (l : list Z) (start : Z) : Prop :=
  MRMinimalRotationAt l start /\
  forall other,
    MRValidStart l other ->
    MRRotationEq l start other ->
    start <= other.

(** Stable mathematical state of the two-candidate elimination phase.

    The unique first minimal start is either one of the two live candidates,
    or it has not yet crossed the monotonically advancing candidate frontier.
    In the latter case the two current rotations cannot already be identical;
    otherwise the first of them would be the canonical answer. *)
