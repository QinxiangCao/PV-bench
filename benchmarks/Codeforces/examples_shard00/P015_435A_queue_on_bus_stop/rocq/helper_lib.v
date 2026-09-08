Require Import PVbench.Codeforces.examples_shard00.P015_435A_queue_on_bus_stop.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition GreedyBusLoading
    (groups : list Z) (capacity : Z) (cuts : list Z) : Prop :=
  ValidBusLoading groups capacity cuts /\
  (forall k, 0 <= k < Zlength cuts - 2 ->
     capacity <
       fold_right Z.add 0
         (sublist (Znth k cuts 0) (Znth (k + 1) cuts 0 + 1) groups)).

Definition GreedyPrefixState
    (groups : list Z) (capacity buses used : Z) : Prop :=
  (groups = nil /\ buses = 1 /\ used = 0) \/
  exists cuts,
    GreedyBusLoading groups capacity cuts /\
    Zlength cuts = buses + 1 /\
    used =
      fold_right Z.add 0
        (sublist (Znth (Zlength cuts - 2) cuts 0) (Zlength groups) groups).
