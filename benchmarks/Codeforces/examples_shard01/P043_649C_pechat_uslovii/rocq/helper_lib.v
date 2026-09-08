Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P043_649C_pechat_uslovii.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition CanPrintAll (pages : list Z) (x y : Z) : Prop :=
  CanPrint pages x y (Zlength pages).

Definition PrefixResourceState
    (pages : list Z)
    (initial_doubles initial_singles processed
     remaining_doubles remaining_singles : Z) : Prop :=
  forall suffix,
    CanPrintAll (sublist 0 processed pages ++ suffix)
      initial_doubles initial_singles <->
    CanPrintAll suffix remaining_doubles remaining_singles.
