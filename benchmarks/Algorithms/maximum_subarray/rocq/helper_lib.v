Require Export PVbench.Algorithms.maximum_subarray.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition max_Z (a b : Z) : Z := Z.max a b.

Definition MaxSuffixSumPrefix (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun lo => 0 <= lo /\ lo < i)
    (fun lo => sum (sublist lo i l))
    ans.

Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
Import SetsNotation.
