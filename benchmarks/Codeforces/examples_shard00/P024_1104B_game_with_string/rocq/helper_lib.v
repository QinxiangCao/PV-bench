Require Import PVbench.Codeforces.examples_shard00.P024_1104B_game_with_string.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition PairDeletionTraceTo
    (initial final : list Z) (moves : Z) : Prop :=
  0 <= moves /\
  exists states,
    Zlength states = moves + 1 /\
    Znth 0 states [] = initial /\
    Znth moves states [] = final /\
    (forall k, 0 <= k < moves ->
       OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states [])).

Definition PairDeletionIrreducible (s : list Z) : Prop :=
  forall next, ~ OneEqualPairDeletion s next.

Definition PrefixGameState
    (prefix reduced : list Z) (moves : Z) : Prop :=
  PairDeletionTraceTo prefix reduced moves /\
  PairDeletionIrreducible reduced /\
  (forall states,
     DeletionGameTrace prefix states ->
     Zlength states = moves + 1).
