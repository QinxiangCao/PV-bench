Require Import PVbench.Algorithms.minimal_representation.rocq.spec_lib.

From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MRCandidateState
    (l : list Z) (best i j : Z) : Prop :=
  best = i \/
  best = j \/
  (Z.max i j <= best /\ ~ MRRotationEq l i j).
