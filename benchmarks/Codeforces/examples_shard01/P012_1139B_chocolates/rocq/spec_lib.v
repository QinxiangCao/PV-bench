(* Codeforces 1139/B - Chocolates: buy as many chocolates as possible when each
   earlier type must be bought either zero times or strictly fewer times. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* x is a legal purchase vector for stock a:
     |x| = |a|
     0 <= x[i] <= a[i]                     you cannot buy more than is in stock
     for all j < i,  x[j] = 0 or x[j] < x[i]   the statement's ordering rule *)
Definition FeasiblePurchase (a x : list Z) : Prop :=
  Zlength x = Zlength a /\
  (forall i, 0 <= i < Zlength a -> 0 <= Znth i x 0 <= Znth i a 0) /\
  (forall j i, 0 <= j < i /\ i < Zlength a -> Znth j x 0 = 0 \/ Znth j x 0 < Znth i x 0).

(* Signature: solve_case(a : list Z) -> Z. *)
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P012 solver Require, so dropped here:
       1 <= Zlength a <= 200000 /\
       Forall (fun x => 1 <= x <= 1000000000) a  *)
  True.

(* out = max { sum(x) : x is a feasible purchase }. *)
Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (fun v => exists x, FeasiblePurchase a x /\ v = (fold_right Z.add 0) x) (fun x => x) out.
