Require Import PVbench.Algorithms.majority_element.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition repeated (candidate vote : Z) : list Z :=
  repeat candidate (Z.to_nat vote).
Definition MajorityOnReduced (major candidate vote : Z) (rest : list Z) : Prop :=
  0 <= vote /\ IsMajorityElement major (repeated candidate vote ++ rest).
