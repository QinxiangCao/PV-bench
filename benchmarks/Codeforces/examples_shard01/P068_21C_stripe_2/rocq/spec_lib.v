(* Codeforces 21/C - Stripe 2: count the ways to cut the stripe into three
   non-empty pieces of equal sum. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P068 solver Require, so dropped here:
       1 <= Zlength a <= 100000 /\
       Forall (fun x => - 10000 <= x <= 10000) a  *)
  True.

(* out = #{ (i, j) : 0 < i < j < n  and
            sum(a[0..i)) = sum(a[i..j)) = sum(a[j..n)) }
   the two cut positions being enumerated by a single index q = i * n + j over
   [0, n^2), with i = q / n and j = q mod n. *)
Definition Spec (a : list Z) (out : Z) : Prop :=
  let n := Zlength a in out = #(fun q : Z => 0 <= q < n * n /\
   let i := q / n in let j := q mod n in 0 < i < j /\ j < n /\
   (fold_right Z.add 0) (sublist 0 i a) = (fold_right Z.add 0) (sublist i j a) /\
   (fold_right Z.add 0) (sublist i j a) = (fold_right Z.add 0) (sublist j n a)).
