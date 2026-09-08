(* Codeforces 460/A - Vasya and Socks: starting with n pairs and receiving one
   every m-th evening, how many consecutive days can he wear socks. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Signature: solve_case(n, m) -> Z.  Pre: 1 <= n <= 100 and 2 <= m <= 100. *)
Definition Pre (n m : Z) : Prop :=
  (* Stated explicitly in the P011 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 100 /\ 2 <= m <= 100. *)
  True.

(* On the morning of day d the stock is n + floor((d-1)/m) - (d-1):
     out > 0
     n + floor((d-1)/m) - (d-1) > 0 for every 1 <= d <= out   a pair each day
     n + floor(out/m) - out = 0                               and none after *)
Definition Spec (n m out : Z) : Prop :=
  out > 0 /\ (forall d, 1 <= d <= out -> n + (d - 1) / m - (d - 1) > 0) /\
  n + out / m - out = 0.
