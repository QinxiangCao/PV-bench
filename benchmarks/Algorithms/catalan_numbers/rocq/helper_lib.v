Require Import PVbench.Algorithms.catalan_numbers.rocq.spec_lib.

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StackRowProgress
    (n : Z) (table : list Z) (row col : Z) : Prop :=
  0 <= row /\
  0 <= col <= n + 1 /\
  StackTablePrefix n table (row * (n + 1) + col).
