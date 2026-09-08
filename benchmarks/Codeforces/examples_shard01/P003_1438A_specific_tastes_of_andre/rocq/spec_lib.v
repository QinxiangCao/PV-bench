(* Codeforces 1438/A - Specific Tastes of Andre: output any perfect array of
   length n. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(n) -> list Z.  Pre: 1 <= n <= 100. *)
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P003 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 100. *)
  True.

(* a is perfect:
     |a| = n
     1 <= a[i] <= 100 for every i
     for all 0 <= l < r <= n,  (r - l) | sum(a[l..r))
   the last clause being the statement's requirement that every non-empty
   subarray is good, its sum divisible by its length. *)
Definition Perfect (n : Z) (a : list Z) : Prop :=
  Zlength a = n /\ Forall (fun x => 1 <= x <= 100) a /\
  forall l r, 0 <= l < r /\ r <= n -> (r - l | (fold_right Z.add 0) (sublist l r a)).

(* out is any perfect array of length n; the property has many witnesses and the
   spec singles out none of them. *)
Definition Spec (n : Z) (out : list Z) : Prop := Perfect n out.

(* Shared yes/no vocabulary: verdict true prints 1, false prints 0. Unused here. *)
Definition VerdictCode (answer : bool) (code : Z) : Prop :=
  (answer = true /\ code = 1) \/
  (answer = false /\ code = 0).
