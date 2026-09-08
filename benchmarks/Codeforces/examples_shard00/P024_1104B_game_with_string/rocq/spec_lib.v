Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition OneEqualPairDeletion (before after : list Z) : Prop :=
  exists i,
    0 <= i < Zlength before - 1 /\
    Znth i before 0 = Znth (i + 1) before 0 /\
    after = sublist 0 i before ++ sublist (i + 2) (Zlength before) before.

Definition DeletionGameTrace (initial : list Z) (states : list (list Z)) : Prop :=
  0 < Zlength states /\ Znth 0 states [] = initial /\
  (forall k, 0 <= k < Zlength states - 1 ->
     OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states [])) /\
  (forall next,
     ~ OneEqualPairDeletion (Znth (Zlength states - 1) states []) next).

Definition FirstPlayerWinsDeletionGame (s : list Z) : Prop :=
  forall states,
    DeletionGameTrace s states ->
    Z.even (Zlength states - 1) = false.

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 100000 /\
  Forall (fun c => 97 <= c <= 122) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> FirstPlayerWinsDeletionGame s).
