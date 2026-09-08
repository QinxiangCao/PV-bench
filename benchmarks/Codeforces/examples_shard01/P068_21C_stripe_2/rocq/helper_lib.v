Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition PrefixSum (a : list Z) (k : Z) : Z :=
  fold_right Z.add 0 (sublist 0 k a).

(* The count of positions [k] in [1, c] whose prefix sum equals [third],
   i.e. how many usable "first cut" candidates the sweep has recorded
   through index [c]. *)

Definition FirstCutCount (a : list Z) (third c : Z) : Z :=
  #(fun k : Z => 1 <= k < c + 1 /\ PrefixSum a k = third).

(* The count of pairs [(k, j)] with [1 <= k < j <= c], [PrefixSum a k = third]
   and [PrefixSum a j = 2 * third], i.e. the count of three-way-equal cut
   pairs whose second cut is at most [c]. *)

Definition ValidPairCount (a : list Z) (third c : Z) : Z :=
  sum_range 1 c
    (fun j => if prop_dec (PrefixSum a j = 2 * third)
              then FirstCutCount a third (j - 1)
              else 0).
