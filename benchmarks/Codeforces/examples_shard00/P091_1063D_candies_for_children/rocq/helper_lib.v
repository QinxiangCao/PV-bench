Require Export PVbench.Codeforces.examples_shard00.P091_1063D_candies_for_children.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition QuotientBlock (k L R q : Z) : Prop :=
  forall num, L <= num <= R -> q = (k - 1) / num.

Definition MaxResult (a b out : Z) : Prop := out = Z.max a b.

Definition MinResult (a b out : Z) : Prop := out = Z.min a b.

Definition CandyArithmeticCandidate
    (n x k num add : Z) : Prop :=
  n <= num <= 2 * n /\
  (add = 0 \/ add = 1) /\
  let q := (k - 1) / num in
  let h := k - x + add - q * num in
  add <= h <= x /\
  h <= num - n /\
  num - n - h <= n - x.

Definition CandySearchPrefix
    (n x k upto best : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : Z * Z =>
       CandyArithmeticCandidate n x k (fst candidate) (snd candidate) /\
       fst candidate < upto)
    (fun candidate => fst candidate - n)
    (-1) best.

Definition CandySearchBlock
    (n x k L R phase best : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : Z * Z =>
       CandyArithmeticCandidate n x k (fst candidate) (snd candidate) /\
       (fst candidate < L \/
        (L <= fst candidate <= R /\ snd candidate < phase)))
    (fun candidate => fst candidate - n)
    (-1) best.

Definition CandyFeasibleInterval
    (n x k L R q add lo hi : Z) : Prop :=
  forall num,
    L <= num <= R ->
    (CandyArithmeticCandidate n x k num add <-> lo <= num <= hi).

Definition CandyArithmeticBest (n x k best : Z) : Prop :=
  CandySearchPrefix n x k (2 * n + 1) best.

Require Import Coq.micromega.Lia.

Require Import Coq.Sorting.Permutation.

Require Import Coq.micromega.Psatz.
