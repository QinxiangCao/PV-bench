(* Codeforces 26/A - Almost Prime: count the integers in [1, n] having exactly two
   distinct prime divisors. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import Coq.ZArith.Znumtheory.

Local Open Scope Z_scope.

(* Signature: solve_case(n) -> Z.  Pre: 1 <= n <= 3000. *)
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P008 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 3000. *)
  True.

(* x has exactly two distinct prime divisors: there are primes p <> q with p | x
   and q | x, and every prime r | x is one of them. *)
Definition AlmostPrime (x : Z) : Prop :=
  exists p q, prime p /\ prime q /\ p <> q /\ (p | x) /\ (q | x) /\
    forall r, prime r -> (r | x) -> r = p \/ r = q.

(* out = #{ x : 1 <= x <= n and AlmostPrime x }. *)
Definition Spec (n out : Z) : Prop :=
  out = #(fun x : Z => 1 <= x < n + 1 /\ AlmostPrime x).
