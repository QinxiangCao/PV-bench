Require Import PVbench.Algorithms.rod_cutting.rocq.spec_lib.

From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition RodCutScanBest
    (price revenue : list Z)
    (rod_len next_piece best : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun piece : Z => 1 <= piece < next_piece)
    (fun piece =>
       Znth piece price 0 + Znth (rod_len - piece) revenue 0)
    0
    best.
