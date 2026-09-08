Require Import PVbench.Algorithms.split_array_largest_sum.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive PrefixSplitState
    (l : list Z) (cap : Z) : Z -> Z -> Z -> Prop :=
  | PrefixSplitState_zero :
      0 <= cap ->
      PrefixSplitState l cap 0 1 0
  | PrefixSplitState_new_segment :
      forall i cnt cur,
        0 <= i < Zlength l ->
        0 <= Znth i l 0 <= cap ->
        cur + Znth i l 0 > cap ->
        PrefixSplitState l cap i cnt cur ->
        PrefixSplitState l cap (i + 1) (cnt + 1) (Znth i l 0)
  | PrefixSplitState_extend :
      forall i cnt cur,
        0 <= i < Zlength l ->
        0 <= Znth i l 0 <= cap ->
        cur + Znth i l 0 <= cap ->
        PrefixSplitState l cap i cnt cur ->
        PrefixSplitState l cap (i + 1) cnt (cur + Znth i l 0).
Definition CanSplit (l : list Z) (m cap : Z) : Prop :=
  exists cnt cur,
    PrefixSplitState l cap (Zlength l) cnt cur /\ cnt <= m.
Definition CannotSplit (l : list Z) (m cap : Z) : Prop :=
  forall cnt cur,
    PrefixSplitState l cap (Zlength l) cnt cur -> m < cnt.
