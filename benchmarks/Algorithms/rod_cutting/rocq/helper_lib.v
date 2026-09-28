Require Export PVbench.Algorithms.rod_cutting.rocq.spec_lib.
From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition RodCutRevenueTable
    (price revenue : list Z) (upto : Z) : Prop :=
  forall rod_len,
    0 <= rod_len < upto ->
    RodCutOptimalRevenue price rod_len (Znth rod_len revenue 0).

Definition RodCutScanBest
    (price revenue : list Z)
    (rod_len next_piece best : Z) : Prop :=
  max_value_of_subset Z.le
    (fun value : Z => value = 0 \/
       exists piece, 1 <= piece < next_piece /\
         value = Znth piece price 0 + Znth (rod_len - piece) revenue 0)
    (fun value => value) best.

From Coq Require Import Lia.
