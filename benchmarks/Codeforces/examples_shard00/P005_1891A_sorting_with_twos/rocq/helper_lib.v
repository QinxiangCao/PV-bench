Require Import PVbench.Codeforces.examples_shard00.P005_1891A_sorting_with_twos.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition NonPowerOfTwo (x : Z) : Prop :=
  ~ exists m : Z, 0 <= m /\ x = Z.pow 2 m.

Definition SortingWithTwosPrefix (a : list Z) (upto : Z) : Prop :=
  forall i, 1 <= i < upto ->
    Znth (i - 1) a 0 <= Znth i a 0 \/
    PowerOfTwoPrefix i (Zlength a).
