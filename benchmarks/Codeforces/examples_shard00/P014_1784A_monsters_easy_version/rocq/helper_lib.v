Require Import PVbench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition PrefixGreedyState
    (original sorted : list Z) (processed kept spent : Z) : Prop :=
  0 <= processed <= Zlength sorted /\
  exists prepared,
    MaximalCascadePreparation (sublist 0 processed sorted) prepared /\
    kept = last prepared 0 /\
    spent = ZListSum (sublist 0 processed sorted) - ZListSum prepared /\
    (processed = Zlength sorted -> Spec original spent).
