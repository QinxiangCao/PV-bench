
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(** Number of queries whose inclusive interval covers [position]. *)
Definition QueryCoverage (queries : list (Z * Z)) (position : Z) : Z :=
  #(fun j : Z =>
      0 <= j < Zlength queries /\
      fst (Znth j queries (0, 0)) <= position <=
      snd (Znth j queries (0, 0))).

(** Mathematical value stored at one index of the range-difference array
    after [done] queries have been incorporated. *)
Definition DifferenceValue
    (queries : list (Z * Z)) (done index : Z) : Z :=
  #(fun j : Z =>
      0 <= j < done /\ fst (Znth j queries (0, 0)) = index) -
  #(fun j : Z =>
      0 <= j < done /\ snd (Znth j queries (0, 0)) + 1 = index).

Definition DifferencePrefix
    (queries : list (Z * Z)) (n done : Z) (diff : list Z) : Prop :=
  Zlength diff = n + 1 /\
  0 <= done <= Zlength queries /\
  forall k, 0 <= k <= n ->
    Znth k diff 0 = DifferenceValue queries done k.

(** Positions before [done] have been converted from differences to exact
    coverage counts; positions from [done] onward retain their difference
    values. *)
Definition CoveragePrefixState
    (queries : list (Z * Z)) (n done : Z) (diff : list Z) : Prop :=
  Zlength diff = n + 1 /\
  1 <= done <= n /\
  (forall k, 0 <= k < done ->
     Znth k diff 0 = QueryCoverage queries k) /\
  (forall k, done <= k <= n ->
     Znth k diff 0 = DifferenceValue queries (Zlength queries) k).

Definition CoverageProfile
    (queries : list (Z * Z)) (n : Z) (coverage : list Z) : Prop :=
  Zlength coverage = n /\
  forall k, 0 <= k < n ->
    Znth k coverage 0 = QueryCoverage queries k.

Definition DotProduct (xs ys : list Z) : Z :=
  fold_right Z.add 0
    (map (fun pair => fst pair * snd pair) (combine xs ys)).

Definition DotProductPrefix
    (xs ys : list Z) (done total : Z) : Prop :=
  0 <= done <= Zlength xs /\
  Zlength xs = Zlength ys /\
  total = DotProduct (sublist 0 done xs) (sublist 0 done ys).
