Require Import PVbench.Algorithms.paint_house_ii.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
From SumLib Require Import Sum ZRange FiniteExtra.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition PaintHouseIIInf : Z := 1000000000.
Inductive PaintHouseIIPrefixCost
    (costs : list (list Z)) (n k : Z) : Z -> Z -> Z -> Prop :=
| PaintHouseIIPrefixCost_nil :
    0 <= n ->
    PaintHouseIIPrefixCost costs n k 0 (-1) 0
| PaintHouseIIPrefixCost_cons :
    forall row prev_color prev_value color value,
      0 <= row < n ->
      0 <= color < k ->
      prev_color <> color ->
      PaintHouseIIPrefixCost costs n k row prev_color prev_value ->
      value = prev_value + PaintCostAt costs row color ->
      PaintHouseIIPrefixCost costs n k (row + 1) color value.
Definition PaintHouseIIBestColor
    (costs : list (list Z)) (n k row color value : Z) : Prop :=
  PaintHouseIIPrefixCost costs n k row color value /\
  min_value_of_subset Z.le
    (fun p : Z * Z =>
       PaintHouseIIPrefixCost costs n k row (fst p) (snd p))
    (fun p : Z * Z => snd p)
    value.
Definition PaintHouseIISecondBestForColor
    (costs : list (list Z)) (n k row color value : Z) : Prop :=
  (row = 0 /\ color = -1 /\ value = 0) \/
  (1 <= row <= n /\
   min_value_of_subset Z.le
     (fun p : Z * Z =>
        fst p <> color /\
        PaintHouseIIPrefixCost costs n k row (fst p) (snd p))
     (fun p : Z * Z => snd p)
     value).
Definition PaintHouseIIDPState
    (costs : list (list Z)) (n k row min1 min2 min1_color : Z) : Prop :=
  (row = 0 /\ min1 = 0 /\ min2 = 0 /\ min1_color = -1) \/
  (1 <= row <= n /\
   0 <= min1_color < k /\
   PaintHouseIIBestColor costs n k row min1_color min1 /\
   PaintHouseIISecondBestForColor costs n k row min1_color min2).
Definition PaintHouseIIPrevSelection
    (old_min1 old_min2 old_color color prev : Z) : Prop :=
  prev = if Z.eq_dec color old_color then old_min2 else old_min1.
Definition PaintHouseIIProcessedCandidate
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color
       processed color value : Z) : Prop :=
  0 <= color < processed /\
  PaintHouseIIPrefixCost costs n k (row + 1) color value.
Definition PaintHouseIIProcessedBestColor
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color processed color value : Z)
    : Prop :=
  PaintHouseIIProcessedCandidate
    costs n k row old_min1 old_min2 old_color processed color value /\
  min_value_of_subset Z.le
    (fun p : Z * Z =>
       PaintHouseIIProcessedCandidate
         costs n k row old_min1 old_min2 old_color processed (fst p) (snd p))
    (fun p : Z * Z => snd p)
    value.
Definition PaintHouseIIProcessedSecondBest
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color processed color value : Z)
    : Prop :=
  min_value_of_subset Z.le
    (fun p : Z * Z =>
       fst p <> color /\
       PaintHouseIIProcessedCandidate
         costs n k row old_min1 old_min2 old_color processed (fst p) (snd p))
    (fun p : Z * Z => snd p)
    value.
Definition PaintHouseIIInnerState
    (costs : list (list Z)) (n k row processed old_min1 old_min2 old_color
       new_min1 new_min2 new_color : Z) : Prop :=
  0 <= row < n /\
  0 <= processed <= k /\
  PaintHouseIIDPState costs n k row old_min1 old_min2 old_color /\
  ((processed = 0 /\
    new_min1 = PaintHouseIIInf /\
    new_min2 = PaintHouseIIInf /\
    new_color = -1) \/
   (1 <= processed <= k /\
    0 <= new_color < processed /\
    PaintHouseIIProcessedBestColor
      costs n k row old_min1 old_min2 old_color processed new_color new_min1 /\
    ((processed = 1 /\ new_min2 = PaintHouseIIInf) \/
     (2 <= processed /\
      PaintHouseIIProcessedSecondBest
        costs n k row old_min1 old_min2 old_color processed new_color new_min2)))).
Definition PaintHouseIICompletedRowState
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color
       new_min1 new_min2 new_color : Z) : Prop :=
  PaintHouseIIInnerState
    costs n k row k old_min1 old_min2 old_color new_min1 new_min2 new_color /\
  PaintHouseIIDPState costs n k (row + 1) new_min1 new_min2 new_color.
