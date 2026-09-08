Require Import PVbench.Algorithms.coin_change.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition DpPrefixZeroed (dp : list Z) (hi : Z) : Prop :=
  0 <= hi /\
  Zlength dp >= hi /\
  Znth 0 dp 0 = 1 /\
  forall k, 1 <= k < hi -> Znth k dp 0 = 0.
Definition DpCoinInnerProgress
    (prev_coins : list Z) (coin : Z) (dp : list Z) (j amount : Z) : Prop :=
  0 < coin /\
  coin <= j /\
  j <= amount + 1 /\
  Zlength dp >= amount + 1 /\
  (forall k,
    0 <= k < j ->
    (Znth k dp 0 <> 0 <->
       ReachableAmount (app prev_coins (cons coin nil)) k)) /\
  forall k,
    j <= k < amount + 1 ->
    (Znth k dp 0 <> 0 <-> ReachableAmount prev_coins k).
Definition NoReachableAbove
    (coins : list Z) (amount res : Z) : Prop :=
  0 <= res <= amount /\
  forall k, res < k <= amount -> ~ ReachableAmount coins k.

Require Import Coq.micromega.Psatz.

(* Helper lemmas migrated from coin_change__vc_proving_subagent_tmp_proof_manual__merged_proof_manual.v. *)
