Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.


(* A mathematical prefix-sum profile.  The first predicate also describes a
   proper prefix while the C construction loop is still filling [pre]. *)
Definition PrefixSumsPrefix (piles prefix : list Z) : Prop :=
  1 <= Zlength prefix <= Zlength piles + 1 /\
  forall i, 0 <= i < Zlength prefix ->
    Znth i prefix 0 =
      sum_range 0 (i - 1) (fun k => Znth k piles 0).

Definition PrefixSums (piles prefix : list Z) : Prop :=
  Zlength prefix = Zlength piles + 1 /\
  forall i, 0 <= i <= Zlength piles ->
    Znth i prefix 0 =
      sum_range 0 (i - 1) (fun k => Znth k piles 0).

(* [r] is the one-based pile containing worm label [q]. *)
Definition PileIndex (piles : list Z) (q r : Z) : Prop :=
  1 <= r <= Zlength piles /\
  sum_range 0 (r - 2) (fun i => Znth i piles 0) < q <=
  sum_range 0 (r - 1) (fun i => Znth i piles 0).

