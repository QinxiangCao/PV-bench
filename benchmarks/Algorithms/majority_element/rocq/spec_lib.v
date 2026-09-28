Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition IsMajorityElement (m : Z) (l : list Z) : Prop :=
  2 * Zlength (filter (Z.eqb m) l) > Zlength l.
