(* Codeforces 65/B - Harry Potter and the History of Magic: rewrite each four-digit
   year by changing at most one digit so the sequence is non-decreasing and lies
   in [1000, 2011], or report No solution. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* d is the four-digit decimal representation of x, most-significant first, with
   d[0] <> 0. *)
Definition FourDigits (x : Z) (d : list Z) : Prop :=
  Zlength d = 4 /\ Forall (fun z => 0 <= z <= 9) d /\ Znth 0 d 0 <> 0 /\
  x = 1000 * Znth 0 d 0 + 100 * Znth 1 d 0 + 10 * Znth 2 d 0 + Znth 3 d 0.

(* y comes from x by changing at most one digit: their four-digit representations
   differ in at most one position. Both being leading-zero-free, the first digit
   can never become 0. *)
Definition AtMostOneDigit (x y : Z) : Prop :=
  exists a b, FourDigits x a /\ FourDigits y b /\ (#(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 <> Znth i b 0)) <= 1.

(* out is an acceptable rewriting of src:
     |out| = |src|
     out is non-decreasing                     chronological order
     1000 <= out[i] <= 2011                    the allowed range
     out[i] differs from src[i] in <= 1 digit *)
Definition ValidYears (src out : list Z) : Prop :=
  Zlength out = Zlength src /\ mono_nondec out /\ Forall (fun y => 1000 <= y <= 2011) out /\
  forall i, 0 <= i < Zlength src -> AtMostOneDigit (Znth i src 0) (Znth i out 0).
Definition Pre (years : list Z) : Prop :=
  (* Stated explicitly in the P056 solver Require, so dropped here:
       1 <= Zlength years <= 1000 /\
       Forall (fun y => 1000 <= y <= 9999) years  *)
  True.

(* out = None     no acceptable rewriting exists, so No solution is printed
   out = Some y   y is one; any acceptable rewriting is accepted *)
Definition Spec (years : list Z) (out : option (list Z)) : Prop :=
  (out = None /\ ~exists y, ValidYears years y) \/ (exists y, out = Some y /\ ValidYears years y).
