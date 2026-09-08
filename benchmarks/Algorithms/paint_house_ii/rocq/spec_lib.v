Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
From SumLib Require Import Sum ZRange FiniteExtra.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition PaintCostAt (costs : list (list Z)) (row color : Z) : Z :=
  Znth color (Znth row costs nil) 0.
Definition PaintHouseIIValidColoring (k n : Z) (colors : list Z) : Prop :=
  Zlength colors = n /\
  (forall i, 0 <= i < n -> 0 <= Znth i colors (-1) < k) /\
  (forall i, 0 <= i < n - 1 ->
     Znth i colors (-1) <> Znth (i + 1) colors (-1)).
Definition PaintHouseIIColoringCost
    (costs : list (list Z)) (n : Z) (colors : list Z) : Z :=
  sum
    (fun i : Z => 0 <= i < n)
    (fun i : Z => PaintCostAt costs i (Znth i colors (-1))).
Definition PaintHouseIIAnswer
    (costs : list (list Z)) (n k answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun colors : list Z =>
       PaintHouseIIValidColoring k n colors)
    (fun colors : list Z =>
       PaintHouseIIColoringCost costs n colors)
    answer.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
