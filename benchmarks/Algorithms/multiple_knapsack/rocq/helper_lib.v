Require Import PVbench.Algorithms.multiple_knapsack.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MKDPValueBound (dp : list Z) (capacity : Z) : Prop :=
  Zlength dp = capacity + 1 /\
  forall cap,
    0 <= cap <= capacity ->
    0 <= Znth cap dp 0 <= 1000000.

(** Pure representation invariant for the three caller-owned scratch arrays.
    It is intentionally independent of every bounded-knapsack semantic
    predicate so that initialization and loop-boundary assertions can retain
    the logical list lengths even when spatial resources are split away. *)
Definition MKTransitionValue
    (old : list Z) (w v cnt capacity pos ans : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= pos <= capacity /\
  Zlength old = capacity + 1 /\
  max_value_of_subset Z.le
    (fun take =>
       0 <= take <= cnt /\
       take * w <= pos /\
       0 <= pos - take * w <= capacity)
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans.
Definition MKTransitionValueBound
    (old : list Z) (w v cnt capacity : Z) : Prop :=
  forall pos ans,
    0 <= pos <= capacity ->
    MKTransitionValue old w v cnt capacity pos ans ->
    0 <= ans <= 1000000.
Definition MKQueueEntryValue
    (old q_idx q_val : list Z) (r w v pos : Z) : Prop :=
  0 <= Znth pos q_idx 0 /\
  r + Znth pos q_idx 0 * w < Zlength old /\
  Znth pos q_val 0 =
    Znth (r + Znth pos q_idx 0 * w) old 0 - Znth pos q_idx 0 * v.
Definition MKQueueEntriesValidAfterDrop
    (old q_idx q_val : list Z) (head tail r w v k cnt : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    k - cnt <= Znth pos q_idx 0 /\
    Znth pos q_idx 0 < k /\
    MKQueueEntryValue old q_idx q_val r w v pos.
Definition MKQueueIndexIncreasing (q_idx : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth p q_idx 0 < Znth q q_idx 0.
Definition MKQueueValueDecreasing (q_val : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth p q_val 0 > Znth q q_val 0.
Definition MKQueueResultValueBound
    (q_val : list Z) (head tail v k : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    0 <= Znth pos q_val 0 + k * v <= 1000000.
Definition MKQueueCoversWindow
    (old q_idx q_val : list Z) (head tail r w v k cnt : Z) : Prop :=
  forall cand,
    0 <= cand ->
    cand < k ->
    k - cnt <= cand ->
    r + cand * w < Zlength old ->
    exists pos,
      head <= pos < tail /\
      cand <= Znth pos q_idx 0 /\
      Znth pos q_idx 0 < k /\
      Znth (r + cand * w) old 0 - cand * v <= Znth pos q_val 0.
Definition MKQueueCoversWithPending
    (old q_idx q_val : list Z) (head tail r w v k cnt current : Z) : Prop :=
  forall cand,
    0 <= cand ->
    cand < k ->
    k - cnt <= cand ->
    r + cand * w < Zlength old ->
    (exists pos,
      head <= pos < tail /\
      cand <= Znth pos q_idx 0 /\
      Znth pos q_idx 0 < k /\
      Znth (r + cand * w) old 0 - cand * v <= Znth pos q_val 0) \/
    Znth (r + cand * w) old 0 - cand * v <= current.
Definition MKQueueEntriesValidForResult
    (old q_idx q_val : list Z) (head tail r w v processed cnt : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    processed - 1 - cnt <= Znth pos q_idx 0 /\
    Znth pos q_idx 0 < processed /\
    MKQueueEntryValue old q_idx q_val r w v pos.
Definition MKQueueCoversResultWindow
    (old q_idx q_val : list Z) (head tail r w v processed cnt : Z) : Prop :=
  forall cand,
    0 <= cand ->
    cand < processed ->
    processed - 1 - cnt <= cand ->
    r + cand * w < Zlength old ->
    exists pos,
      head <= pos < tail /\
      cand <= Znth pos q_idx 0 /\
      Znth pos q_idx 0 < processed /\
      Znth (r + cand * w) old 0 - cand * v <= Znth pos q_val 0.
Definition MKZeroPrefixSafety (dp : list Z) (hi : Z) : Prop :=
  0 <= hi /\ Zlength dp = hi.
Definition MKZeroPrefixSemantics (dp : list Z) (hi : Z) : Prop :=
  forall cap, 0 <= cap < hi -> Znth cap dp 0 = 0.
Definition MKCopyPrefixSafety
    (src dst : list Z) (j capacity : Z) : Prop :=
  0 <= j <= capacity + 1 /\
  Zlength src = capacity + 1 /\
  Zlength dst = capacity + 1.
Definition MKCopyPrefixSemantics
    (src dst : list Z) (j : Z) : Prop :=
  forall cap, 0 <= cap < j -> Znth cap dst 0 = Znth cap src 0.
Definition MKTransitionSafety
    (old : list Z) (w cnt capacity pos : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= pos <= capacity /\
  Zlength old = capacity + 1.
Definition MKTransitionSemantics
    (old : list Z) (w v cnt capacity pos ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun take =>
       0 <= take <= cnt /\
       take * w <= pos /\
       0 <= pos - take * w <= capacity)
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans.
Definition MKItemResidueProgressSafety
    (old dp : list Z) (r w cnt capacity : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= r /\
  r <= w /\
  r <= capacity + 1 /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1.
Definition MKItemResidueProgressSemantics
    (old dp : list Z) (r w v cnt capacity : Z) : Prop :=
  (forall rem k pos,
     pos = rem + k * w ->
     0 <= rem < r ->
     0 <= k ->
     0 <= pos <= capacity ->
     MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) /\
  (forall rem k pos,
     pos = rem + k * w ->
     r <= rem < w ->
     0 <= k ->
     0 <= pos <= capacity ->
     Znth pos dp 0 = Znth pos old 0).
Definition MKItemResiduePrefixSafety
    (old dp : list Z) (r w cnt k capacity : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= r < w /\
  0 <= k /\
  r <= capacity /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1.
Definition MKItemResiduePrefixSemantics
    (old dp : list Z) (r w v cnt k capacity : Z) : Prop :=
  (forall t,
     0 <= t < k ->
     r + t * w <= capacity ->
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) /\
  forall pos,
    0 <= pos <= capacity ->
    (forall rem t,
       pos = rem + t * w ->
       0 <= rem < r ->
       0 <= t ->
       MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) /\
    (forall rem t,
       pos = rem + t * w ->
       0 <= rem < w ->
       0 <= t ->
       (r < rem \/ (rem = r /\ k <= t)) ->
       Znth pos dp 0 = Znth pos old 0).
Definition MKQueueStorageSafety
    (old q_idx q_val : list Z) (head tail limit capacity : Z) : Prop :=
  0 <= head <= tail /\
  tail <= limit /\
  tail <= Zlength q_idx /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1 /\
  Zlength old = capacity + 1.
Definition MKQueueDropSafety
    (old q_idx q_val : list Z)
    (head tail r w k capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  MKQueueStorageSafety old q_idx q_val head tail k capacity.
Definition MKQueueDropSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt k : Z) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt /\
  MKQueueResultValueBound q_val head tail v (k - 1).
Definition MKQueueAfterDropSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt k : Z) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt /\
  MKQueueResultValueBound q_val head tail v k.
Definition MKQueuePendingSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt k current : Z) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWithPending old q_idx q_val head tail r w v k cnt current /\
  MKQueueResultValueBound q_val head tail v k /\
  0 <= current + k * v <= 1000000.
Definition MKQueueResultSafety
    (old q_idx q_val : list Z)
    (head tail r w processed capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= processed /\
  MKQueueStorageSafety old q_idx q_val head tail processed capacity.
Definition MKQueueResultSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt processed capacity : Z) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v processed cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversResultWindow old q_idx q_val head tail r w v processed cnt /\
  MKQueueResultValueBound q_val head tail v (processed - 1) /\
  (head < tail ->
     MKTransitionSemantics old w v cnt capacity (r + (processed - 1) * w)
       (Znth head q_val 0 + (processed - 1) * v)).
Definition MKResidueLoopSafety
    (old dp q_idx q_val : list Z)
    (r w k head tail capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  0 <= head <= tail /\
  tail <= k /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1 /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1.
Definition MKResidueLoopSemantics
    (old dp q_idx q_val : list Z)
    (r w v cnt k head tail capacity : Z) : Prop :=
  (forall t,
     0 <= t < k ->
     r + t * w <= capacity ->
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) /\
  MKQueueResultSemantics old q_idx q_val head tail r w v cnt k capacity.

(* Helper imports migrated from multiple_knapsack__vc_proving_round9_merged_proof_manual.v. *)
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

(* Helper lemmas migrated from multiple_knapsack__vc_proving_round9_merged_proof_manual.v. *)
