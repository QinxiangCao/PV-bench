Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.
Require Import PVbench.Codeforces.examples_shard01.P030_1220C_substring_game_in_the_lesson.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition PrefixMinimum (s : list Z) (k mn : Z) : Prop :=
  0 <= k <= Zlength s /\
  ((k = 0 /\ mn = 123) \/
   (0 < k /\
    (exists j, 0 <= j < k /\ mn = Znth j s 0) /\
    forall j, 0 <= j < k -> mn <= Znth j s 0)).

Definition SpecPrefix (s : list Z) (k : Z) (out : list Z) : Prop :=
  Zlength out = k /\
  forall i, 0 <= i < k ->
    ((Znth i out 0 = 1 /\ AnnWins s i) \/
     (Znth i out 0 = 0 /\ ~ AnnWins s i)).

