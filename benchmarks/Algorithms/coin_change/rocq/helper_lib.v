Require Export PVbench.Algorithms.coin_change.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition DpPrefixZeroed (dp : list Z) (hi : Z) : Prop :=
  Znth 0 dp 0 = 1 /\ Forall (eq 0) (sublist 1 hi dp).

(* Boolean output format is part of the requested table semantics. *)
Definition DpReachableTable (coins : list Z) (dp : list Z) (hi : Z) : Prop :=
  Forall (fun flag => flag = 0 \/ flag = 1) dp /\
  forall k, 0 <= k < hi -> (Znth k dp 0 <> 0 <-> ReachableAmount coins k).

Definition DpCoinInnerProgress
    (prev_coins : list Z) (coin : Z) (dp : list Z) (j amount : Z) : Prop :=
  Forall (fun flag => flag = 0 \/ flag = 1) dp /\
  (forall k, 0 <= k < j ->
    (Znth k dp 0 <> 0 <-> ReachableAmount (prev_coins ++ [coin]) k)) /\
  forall k, j <= k < amount + 1 ->
    (Znth k dp 0 <> 0 <-> ReachableAmount prev_coins k).

Definition NoReachableAbove (coins : list Z) (amount res : Z) : Prop :=
  forall k, res < k <= amount -> ~ ReachableAmount coins k.
