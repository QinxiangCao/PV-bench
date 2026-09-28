Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
From SumLib Require Import ZRange.

Definition same_colorb (colors : list Z) (a b : Z) : bool :=
  Z.eqb (Znth a colors 0) (Znth b colors 0).

(** Public count definitions use Z-indexed library enumeration and Zlength.
    Closed coffee-shop intervals [lo, hi] use Zrange lo (hi + 1). *)
Definition InnsAffordable (costs : list Z) (p lo hi : Z) : bool :=
  existsb (fun idx => Z.leb (Znth idx costs 0) p) (Zrange lo (hi + 1)).

Definition InnsPairAllowed (colors costs : list Z) (p : Z) (pair : Z * Z) : bool :=
  let (left, right) := pair in
  same_colorb colors left right && InnsAffordable costs p left right.

Definition InnsPairs (n : Z) : list (Z * Z) :=
  flat_map (fun right => map (fun left => (left, right)) (Zrange 0 right)) (Zrange 0 n).

Definition InnsPairCount (colors costs : list Z) (p n : Z) : Z :=
  Zlength (filter (InnsPairAllowed colors costs p) (InnsPairs n)).

Definition InnsPairAnswer (colors costs : list Z) (n p answer : Z) : Prop :=
  answer = InnsPairCount colors costs p n.
