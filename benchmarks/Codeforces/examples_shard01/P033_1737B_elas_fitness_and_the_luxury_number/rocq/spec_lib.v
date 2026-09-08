(* Codeforces 1737/B - Ela's Fitness and the Luxury Number: count the luxurious
   numbers in [l, r], x being luxurious when floor(sqrt x) divides x. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* x is luxurious: its integer square root q, the q > 0 with q^2 <= x < (q+1)^2,
   divides x. *)
Definition Luxury (x : Z) : Prop :=
  exists q, q > 0 /\ q * q <= x < (q + 1) * (q + 1) /\ (q | x).

Definition Pre (l r : Z) : Prop :=
  (* Every clause below is stated explicitly in the P033 solver Require, which
     therefore omits the Pre(...) call:
       1 <= l <= r /\ r <= Z.pow 10 18. *)
  True.

(* out = #{ x : l <= x <= r and x is luxurious }. *)
Definition Spec (l r out : Z) : Prop :=
  out = #(fun x : Z => l <= x < r + 1 /\ Luxury x).
