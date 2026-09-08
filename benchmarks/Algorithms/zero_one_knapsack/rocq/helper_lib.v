Require Import PVbench.Algorithms.zero_one_knapsack.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition KnapsackStaticSafety
    (weights values : list Z) (item_count capacity width : Z) : Prop :=
  0 <= item_count <= 300 /\
  0 <= capacity <= 300 /\
  width = capacity + 1 /\
  1 <= width <= 301 /\
  KnapsackInputsBounded weights values item_count capacity.
Definition KnapsackRowProgress
    (weights values : list Z) (capacity : Z) (dp : list Z)
    (row col : Z) : Prop :=
  KnapsackTablePrefix weights values capacity dp
    (row * (capacity + 1) + col).
Definition KnapsackRowsAnnotationState
    (weights values : list Z) (item_count capacity width : Z)
    (dp : list Z) (rows_done : Z) : Prop :=
  KnapsackStaticSafety weights values item_count capacity width /\
  0 <= rows_done <= item_count + 1 /\
  0 <= rows_done * width <= (item_count + 1) * (capacity + 1) /\
  KnapsackTablePrefixShape dp (rows_done * width) /\
  KnapsackTableValuesBounded dp /\
  KnapsackRowsDone weights values capacity dp rows_done.
Definition KnapsackRowAnnotationState
    (weights values : list Z) (item_count capacity width : Z)
    (dp : list Z) (row col : Z) : Prop :=
  KnapsackStaticSafety weights values item_count capacity width /\
  0 <= row <= item_count /\
  0 <= col <= capacity + 1 /\
  0 <= row * width + col <= (item_count + 1) * (capacity + 1) /\
  KnapsackTablePrefixShape dp (row * width + col) /\
  KnapsackTableValuesBounded dp /\
  KnapsackRowProgress weights values capacity dp row col.
