Require Export PVbench.Algorithms.sliding_window_maximum.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
Require Import MaxMinLib.MaxMin.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition SWMOutputPrefix
    (l : list Z) (k out_idx : Z) (out : list Z) : Prop :=
  forall idx,
    0 <= idx < out_idx ->
    WindowMaxValue l idx (idx + k) (Znth idx out 0).

Definition SWMQueueEntriesInWindow
    (q_l : list Z) (head tail lo hi : Z) : Prop :=
  Forall (fun idx => lo <= idx < hi) (sublist head tail q_l).

Definition SWMQueueEntriesInOpenWindow
    (q_l : list Z) (head tail lo hi : Z) : Prop :=
  Forall (fun idx => lo < idx < hi) (sublist head tail q_l).

Definition SWMQueueIndexIncreasing (q_l : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth p q_l 0 < Znth q q_l 0.

Definition SWMQueueValueDecreasing
    (l q_l : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth (Znth p q_l 0) l 0 > Znth (Znth q q_l 0) l 0.

Definition SWMQueueCoversWindow
    (l q_l : list Z) (head tail lo hi : Z) : Prop :=
  forall idx,
    0 <= idx < Zlength l ->
    lo <= idx < hi ->
    exists pos,
      head <= pos < tail /\
      idx <= Znth pos q_l 0 < hi /\
      Znth idx l 0 <= Znth (Znth pos q_l 0) l 0.

Definition SWMQueueCoversOpenWindow
    (l q_l : list Z) (head tail lo hi : Z) : Prop :=
  forall idx,
    0 <= idx < Zlength l ->
    lo < idx < hi ->
    exists pos,
      head <= pos < tail /\
      idx <= Znth pos q_l 0 < hi /\
      Znth idx l 0 <= Znth (Znth pos q_l 0) l 0.

Definition SWMQueueCoversWithPending
    (l q_l : list Z) (head tail lo i : Z) : Prop :=
  forall idx,
    0 <= idx < Zlength l ->
    lo < idx < i ->
    (exists pos,
      head <= pos < tail /\
      idx <= Znth pos q_l 0 < i /\
      Znth idx l 0 <= Znth (Znth pos q_l 0) l 0) \/
    Znth idx l 0 <= Znth i l 0.

Definition SWMQueueDropLoopState
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  SWMQueueEntriesInWindow q_l head tail (i - k) i /\
  SWMQueueIndexIncreasing q_l head tail /\
  SWMQueueValueDecreasing l q_l head tail /\
  SWMQueueCoversOpenWindow l q_l head tail (i - k) i.

Definition SWMQueuePendingState
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  SWMQueueEntriesInOpenWindow q_l head tail (i - k) i /\
  SWMQueueIndexIncreasing q_l head tail /\
  SWMQueueValueDecreasing l q_l head tail /\
  SWMQueueCoversWithPending l q_l head tail (i - k) i.

Definition SWMQueueState
    (l q_l : list Z) (head tail processed k : Z) : Prop :=
  SWMQueueEntriesInWindow q_l head tail (processed - k) processed /\
  SWMQueueIndexIncreasing q_l head tail /\
  SWMQueueValueDecreasing l q_l head tail /\
  SWMQueueCoversWindow l q_l head tail (processed - k) processed /\
  (head < tail /\ k <= processed ->
    WindowMaxValue l (processed - k) processed
      (Znth (Znth head q_l 0) l 0)).
