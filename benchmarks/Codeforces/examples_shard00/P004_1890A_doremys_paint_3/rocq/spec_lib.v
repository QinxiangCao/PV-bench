Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition GoodAdjacentSums (b : list Z) : Prop :=
  exists k, forall i,
    0 <= i < Zlength b - 1 ->
    Znth i b 0 + Znth (i + 1) b 0 = k.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 100 /\
  Forall (fun x => 1 <= x <= 100000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists b, Permutation a b /\ GoodAdjacentSums b).
