Require Import PVbench.Algorithms.rmq.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition RMQInputValues (l : list Z) (n : Z) : Prop :=
  Zlength l = n /\
  forall i, 0 <= i < n -> -2147483648 <= Znth i l 0 <= 2147483647.
Definition STCellBounds (st_ls : list Z) (K i j : Z) : Prop :=
  0 < K /\
  0 <= i /\
  0 <= j /\ j < K /\
  0 <= i * K + j < Zlength st_ls.
Definition STZeroPrefixBounds (st_ls : list Z) (upto : Z) : Prop :=
  0 <= upto /\ upto <= Zlength st_ls.
Definition STBasePrefixBounds (n upto : Z) : Prop :=
  0 <= upto /\ upto <= n.
Definition STLevelPrefixBounds (K n j upto : Z) : Prop :=
  0 <= j /\ j < K /\ 0 <= upto /\ upto <= n.
Definition STZeroPrefix (st_ls : list Z) (upto : Z) : Prop :=
  forall p, 0 <= p < upto -> Znth p st_ls 0 = 0.
Definition STBasePrefix
    (l st_ls : list Z) (K n upto : Z) : Prop :=
  forall i, 0 <= i < upto -> STCellRangeMax l st_ls K i 0.
Definition STLevelPrefix
    (l st_ls : list Z) (K n j upto : Z) : Prop :=
  forall i,
    0 <= i /\ i < upto /\ i + Power2 j <= n ->
    STCellRangeMax l st_ls K i j.
Definition QueryLogBounds (K n len k pow : Z) : Prop :=
  1 <= len /\
  len <= n /\
  1 <= K /\
  n < Power2 K /\
  0 <= k /\
  k < K /\
  1 <= pow.

(** Mathematical progress of the integer-logarithm loop, independent of the
    enclosing C bounds used to justify arithmetic and table access. *)
Definition QueryLogLoopState (len k pow : Z) : Prop :=
  0 <= k /\
  pow = Power2 k /\
  Power2 k <= len.
Definition QueryLogFinalState (len k pow : Z) : Prop :=
  QueryLogLoopState len k pow /\
  len < Power2 (k + 1).

(* Helper imports migrated from rmq__vc_proving_subagent_merged_proof_manual.v. *)
