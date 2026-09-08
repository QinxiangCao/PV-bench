(* Codeforces 474/B - Worms: worms are numbered consecutively pile by pile; for
   each queried label, print which pile it falls in. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Every query is a valid label, 1 <= q <= sum(piles); the length and value bounds
   are stated in the solver Require instead, so they are commented out here. *)
Definition Pre (piles queries : list Z) : Prop :=
  (* 1 <= Zlength piles <= 100000 /\ 1 <= Zlength queries <= 100000 /\
  Forall (fun x => 1 <= x <= 1000) piles /\ *)
  Forall (fun q => 1 <= q <= (fold_right Z.add 0) piles) queries.

(* One answer per query, |out| = |queries|, with out[j] the pile holding worm
   q[j]:
     1 <= out[j] <= |piles|
     piles[0] + ... + piles[out[j]-2]  <  q[j]  <=  piles[0] + ... + piles[out[j]-1]
   i.e. the labels before that pile fall short of q[j] and the labels through it
   reach it. *)
Definition Spec (piles queries out : list Z) : Prop :=
  Zlength out = Zlength queries /\ forall j, 0 <= j < Zlength queries ->
    1 <= Znth j out 0 <= Zlength piles /\
    sum_range 0 (Znth j out 0 - 2) (fun i => Znth i piles 0) < Znth j queries 0 <=
    sum_range 0 (Znth j out 0 - 1) (fun i => Znth i piles 0).
