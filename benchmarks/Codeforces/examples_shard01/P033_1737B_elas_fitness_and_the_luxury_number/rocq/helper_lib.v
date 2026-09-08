Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P033_1737B_elas_fitness_and_the_luxury_number.rocq.spec_lib.

Local Open Scope Z_scope.

Definition ISqrtSpec (v root : Z) : Prop :=
  0 <= root /\ root * root <= v < (root + 1) * (root + 1).

Definition LuxuryCountUpto (x out : Z) : Prop :=
  out = #(fun z : Z => 1 <= z < x + 1 /\ Luxury z).

Definition SqrtSearchBounds (v lo hi : Z) : Prop :=
  lo * lo <= v /\ v < (hi + 1) * (hi + 1).

Definition LuxuryBlockPrefix (x s m cnt : Z) : Prop :=
  cnt = 3 * (s - 1) +
    #(fun k : Z => 0 <= k < m /\ s * s + k * s <= x).
