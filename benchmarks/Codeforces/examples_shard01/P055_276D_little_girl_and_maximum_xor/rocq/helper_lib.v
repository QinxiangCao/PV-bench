Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition HighestBitScan (l r x b : Z) : Prop :=
  x = Z.lxor l r /\
  forall k, b < k <= 63 -> Z.land (Z.shiftr x k) 1 = 0.
