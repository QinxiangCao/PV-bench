Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P012_1139B_chocolates.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* A dominant purchase is a mathematical upper envelope of all legal purchase
   vectors for the same ordered stock list.  It is independent of the C loop:
   any implementation producing such a vector attains the optimum. *)
Definition DominantPurchase (a x : list Z) : Prop :=
  FeasiblePurchase a x /\
  forall y,
    FeasiblePurchase a y ->
    forall k, 0 <= k < Zlength a -> Znth k y 0 <= Znth k x 0.

(* The loop has already fixed the suffix beginning at [lo].  [total] is its
   sum and [prev] is its leftmost chosen amount (or zero for the empty suffix),
   which is exactly the boundary that constrains the next item to the left. *)
Definition SuffixDominantState
    (a : list Z) (lo total prev : Z) : Prop :=
  exists x,
    DominantPurchase (sublist lo (Zlength a) a) x /\
    total = fold_right Z.add 0 x /\
    (lo = Zlength a -> prev = 0) /\
    (lo < Zlength a -> prev = Znth 0 x 0).
