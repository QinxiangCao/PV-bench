Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
From SumLib Require Import Sum ZRange FiniteExtra.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
(** Keep the element type implicit when Zlength is passed to map. *)
Arguments Zlength {A}.

Definition PaintCostAt (costs : list (list Z)) (row color : Z) : Z :=
  Znth color (Znth row costs nil) 0.

Definition PaintHouseIIColoringCost
    (costs : list (list Z)) (n : Z) (colors : list Z) : Z :=
  sum
    (fun i : Z => 0 <= i < n)
    (fun i : Z => PaintCostAt costs i (Znth i colors (-1))).

(** Mathematical contracts exposed to C; execution bounds remain explicit in
    the annotation.  Existing proof-support definitions above are unchanged. *)
Definition PaintHouseIILegalColoring (k n : Z) (colors : list Z) : Prop :=
  Zlength colors = n /\
  Forall (fun color => 0 <= color < k) colors /\
  (forall i, 0 <= i < n - 1 ->
    Znth i colors (-1) <> Znth (i + 1) colors (-1)).

Definition PaintHouseIIOptimalCost (costs : list (list Z)) (n k answer : Z) : Prop :=
  min_value_of_subset Z.le (PaintHouseIILegalColoring k n)
    (PaintHouseIIColoringCost costs n) answer.
