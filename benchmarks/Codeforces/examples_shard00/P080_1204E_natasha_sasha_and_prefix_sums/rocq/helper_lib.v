Require Export PVbench.Codeforces.examples_shard00.P080_1204E_natasha_sasha_and_prefix_sums.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Require Import Coq.Arith.Factorial.

Definition P080Factorial (n : Z) : Z := Z.of_nat (fact (Z.to_nat n)).

Definition P080Factorials (fl : list Z) (hi : Z) : Prop :=
  forall j, 0 <= j < hi -> Znth j fl 0 = P080Factorial j mod 998244853.

Definition P080InverseFactorials (il : list Z) (lo hi : Z) : Prop :=
  forall j, lo <= j < hi ->
    Znth (j - lo) il 0 = Z.pow (P080Factorial j) 998244851 mod 998244853.

Definition P080ZeroCount (n m : Z) : Z :=
  sum
    (fun candidate : list Z * Z =>
      ((Zlength (fst candidate) = n + m /\ Forall IsSign (fst candidate)) /\
       0 <= snd candidate < n + 1) /\
      IsArrayMaximumCandidate n m candidate /\ snd candidate = 0)
    (fun _ => 1) mod 998244853.

Definition P080Tables (n m x y : Z) (kl dl : list Z) : Prop :=
  forall r c, 0 <= r <= n -> 0 <= c <= m ->
    (r < x \/ r = x /\ c < y ->
       Znth (r * (m + 1) + c) kl 0 = P080ZeroCount r c /\
       Spec r c (Znth (r * (m + 1) + c) dl 0)) /\
    (x < r \/ r = x /\ y <= c ->
       Znth (r * (m + 1) + c) kl 0 = 0 /\
       Znth (r * (m + 1) + c) dl 0 = 0).

Require Import Coq.micromega.Lia.

Require Import Coq.ZArith.Zpow_facts.

Require Import Coq.micromega.Psatz.
