Require Import PVbench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition PrefixSummary
    (a : list Z) (i total least : Z) : Prop :=
  0 <= i <= Zlength a /\
  total = TotalPower (sublist 0 i a) /\
  ((i = 0 /\ least = 101) \/
   (0 < i /\
    exists least_index,
      0 <= least_index < i /\
      least = Znth least_index a 0 /\
      forall k, 0 <= k < i -> least <= Znth k a 0)).

Definition EnumeratedCost
    (a : list Z) (total least i x cost : Z) : Prop :=
  cost = total \/
  exists source factor,
    0 <= source < Zlength a /\
    2 <= factor <= Znth source a 0 /\
    (factor | Znth source a 0) /\
    (source < i \/ (source = i /\ factor < x)) /\
    cost = total - Znth source a 0 - least +
           Znth source a 0 / factor + least * factor.

Definition SearchMinimum
    (a : list Z) (total least i x answer : Z) : Prop :=
  min_value_of_subset Z.le
    (EnumeratedCost a total least i x) (fun cost => cost) answer.
