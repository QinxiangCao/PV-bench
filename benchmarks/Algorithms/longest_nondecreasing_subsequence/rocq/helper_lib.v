Require Import PVbench.Algorithms.longest_nondecreasing_subsequence.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition LastValueOf (l idxs : list Z) (v : Z) : Prop :=
  0 < Zlength idxs /\
  v = Znth (Znth (Zlength idxs - 1) idxs 0) l 0.

(* Data representation for the initialized prefix of the caller-owned
   workspace.  It deliberately says nothing about LNDS optimality. *)
Definition LNDTailsRepresentation (tails : list Z) (len : Z) : Prop :=
  Zlength tails = len /\
  increasing tails.

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

(* Each realized frontier entry is the minimum possible tail among
   subsequences of the same length. *)
Definition LNDTailsMinimality
    (l : list Z) (i : Z) (tails : list Z) (len : Z) : Prop :=
  forall idxs k v,
    ValidNondecreasingSubsequence l i idxs ->
    Zlength idxs = k + 1 ->
    0 <= k < len ->
    LastValueOf l idxs v ->
    Znth k tails 0 <= v.

(* Compatibility predicate used only by the established transition lemmas.
   C annotations use the finer public layers above. *)
Definition UpperBoundPartition
    (tails : list Z) (len x left right : Z) : Prop :=
  (forall k, 0 <= k < left -> Znth k tails 0 <= x) /\
  (forall k, right <= k < len -> x < Znth k tails 0).
