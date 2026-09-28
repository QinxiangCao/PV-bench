Require Export PVbench.Algorithms.longest_nondecreasing_subsequence.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.micromega.Psatz.

Definition LastValueOf (l idxs : list Z) (v : Z) : Prop :=
  0 < Zlength idxs /\
  v = Znth (Znth (Zlength idxs - 1) idxs 0) l 0.

(* Every stored tail is realized by a subsequence of the corresponding
   length in the processed input prefix. *)
Definition LNDTailsRealizability
    (l : list Z) (i : Z) (tails : list Z) (len : Z) : Prop :=
  forall k,
    0 <= k < len ->
    exists idxs,
      ValidNondecreasingSubsequence l i idxs /\
      Zlength idxs = k + 1 /\
      LastValueOf l idxs (Znth k tails 0).

(* Optimal output length for the processed prefix. *)
Definition LNDSOptimalLength (l : list Z) (i len : Z) : Prop :=
  LNDSLengthPrefix l i len.

(** Public mathematical tail properties; workspace lengths stay outside. *)
Definition LNDTailsRepresentation (tails : list Z) (_len : Z) : Prop :=
  increasing tails.

Definition LNDTailsMinimality (l : list Z) (i : Z) (tails : list Z) (len : Z) : Prop :=
  forall k, 0 <= k < len ->
    min_value_of_subset Z.le
      (fun v => exists idxs, ValidNondecreasingSubsequence l i idxs /\
        Zlength idxs = k + 1 /\ LastValueOf l idxs v)
      (fun v : Z => v) (Znth k tails 0).

(** The search partition describes the values in each segment, independently
    of their positions.  The indexed view above supports existing helpers. *)
Definition UpperBoundPartition
    (tails : list Z) (len x left right : Z) : Prop :=
  Forall (Z.ge x) (sublist 0 left tails) /\
  Forall (Z.lt x) (sublist right len tails).
