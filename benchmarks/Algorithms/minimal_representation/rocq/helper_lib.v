Require Export PVbench.Algorithms.minimal_representation.rocq.spec_lib.
From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Require Import MaxMinLib.MaxMin.
From Coq Require Import Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
From Coq Require Import Lia.

(** Stable mathematical state of the two-candidate elimination phase.

    The unique first minimal start is either one of the two live candidates,
    or it has not yet crossed the monotonically advancing candidate frontier.
    In the latter case the two current rotations cannot already be identical;
    otherwise the first of them would be the canonical answer. *)
Definition MRCandidateState
    (l : list Z) (best i j : Z) : Prop :=
  best = i \/
  best = j \/
  (Z.max i j <= best /\ ~ MRRotationEq l i j).
