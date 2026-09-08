Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint count (m : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x m then 1 else 0) + count m xs
  end.
Definition IsMajorityElement (m : Z) (l : list Z) : Prop :=
  2 * (count m l) > Z.of_nat (length l).
