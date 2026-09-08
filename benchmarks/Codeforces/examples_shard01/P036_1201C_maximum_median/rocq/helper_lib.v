Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P036_1201C_maximum_median.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition MedianRaiseCost (sorted : list Z) (m : Z) : Z :=
  fold_right Z.add 0
    (map (fun x => Z.max 0 (m - x))
         (sublist (Zlength sorted / 2) (Zlength sorted) sorted)).

Definition MedianCostPrefix
    (sorted : list Z) (m i need : Z) : Prop :=
  need = fold_right Z.add 0
    (map (fun x => Z.max 0 (m - x))
         (sublist (Zlength sorted / 2) i sorted)).

Definition MedianSearchBounds
    (values : list Z) (k lo hi : Z) : Prop :=
  ReachMedian values k lo /\
  forall candidate, hi < candidate -> ~ ReachMedian values k candidate.
