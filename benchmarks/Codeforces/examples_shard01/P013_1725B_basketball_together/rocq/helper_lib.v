Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition TeamNeed (D power : Z) : Z := D / power + 1.

Definition BasketballGreedyPrefix
    (sorted : list Z) (D done used : Z) : Prop :=
  used = fold_right Z.add 0
    (map (TeamNeed D) (sublist 0 done sorted)).
