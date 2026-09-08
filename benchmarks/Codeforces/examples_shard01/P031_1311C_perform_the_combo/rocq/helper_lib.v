Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P031_1311C_perform_the_combo.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition DifferencePrefix
    (tries : list Z) (n i : Z) (diff_values : list Z) : Prop :=
  Zlength diff_values = n + 1 /\
  Znth 0 diff_values 0 = i /\
  forall k, 1 <= k <= n ->
    Znth k diff_values 0 = - Count k (sublist 0 i tries).

Definition DifferenceReady
    (tries : list Z) (n : Z) (diff_values : list Z) : Prop :=
  Zlength diff_values = n + 1 /\
  Znth 0 diff_values 0 = Zlength tries + 1 /\
  forall k, 1 <= k <= n ->
    Znth k diff_values 0 = - Count k tries.

Definition PartialSpec
    (s tries : list Z) (done : Z) (out : list Z) : Prop :=
  Zlength out = 26 /\
  forall c, 97 <= c <= 122 ->
    Znth (c - 97) out 0 =
      Count c (sublist 0 done s) +
      (fold_right Z.add 0)
        (map (fun p => Count c (sublist 0 (Z.min p done) s)) tries).

