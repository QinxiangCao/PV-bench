Require Export PVbench.Codeforces.examples_shard00.P017_887A_div_64.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition PrefixScan (prefix : list Z) (seen_one zeros : Z) : Prop :=
  (seen_one = 0 /\ zeros = 0 /\ ~ In 49 prefix) \/
  (seen_one = 1 /\ exists before after,
    prefix = before ++ 49 :: after /\
    ~ In 49 before /\
    zeros = Z.of_nat (count_occ Z.eq_dec after 48)).

Require Import Coq.micromega.Lia.
