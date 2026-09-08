(* Codeforces 1492/D - Genius's Gambit: find binary x >= y, each made of a zeroes
   and b ones, whose difference has exactly k ones, or report No. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Value of a binary digit list, most-significant first. *)
Definition BinaryValue (d : list Z) : Z := fold_left (fun a b => 2 * a + b) d 0.

(* d is the canonical binary representation of v: non-empty, 0/1 digits, value v,
   and either v = 0 with d = [0] or v > 0 with leading digit 1. *)
Definition BinaryRep (v : Z) (d : list Z) : Prop :=
  d <> [] /\ Forall (fun z => z = 0 \/ z = 1) d /\ BinaryValue d = v /\
  ((v = 0 /\ d = [0]) \/ (v > 0 /\ Znth 0 d 0 = 1)).

(* (x, y) is a valid answer:
     |x| = |y| = a + b, all digits 0 or 1
     x and y each contain exactly a zeroes and b ones
     x[0] = y[0] = 1                         no leading zeroes
     value(x) >= value(y)
     the binary representation of value(x) - value(y) has exactly k ones *)
Definition GambitPair (a b k : Z) (q : list Z * list Z) : Prop :=
  let ' (x, y) := q in Zlength x = a + b /\ Zlength y = a + b /\
  Forall (fun z => z = 0 \/ z = 1) x /\ Forall (fun z => z = 0 \/ z = 1) y /\
  (#(fun i : Z => 0 <= i < Zlength x /\ Znth i x 0 = 0)) = a /\ (#(fun i : Z => 0 <= i < Zlength x /\ Znth i x 0 = 1)) = b /\ (#(fun i : Z => 0 <= i < Zlength y /\ Znth i y 0 = 0)) = a /\ (#(fun i : Z => 0 <= i < Zlength y /\ Znth i y 0 = 1)) = b /\
  Znth 0 x 0 = 1 /\ Znth 0 y 0 = 1 /\ BinaryValue x >= BinaryValue y /\
  exists diff, BinaryRep (BinaryValue x - BinaryValue y) diff /\ (#(fun i : Z => 0 <= i < Zlength diff /\ Znth i diff 0 = 1)) = k.
Definition Pre (a b k : Z) : Prop :=
  (* Every clause below is stated explicitly in the P062 solver Require, which
     therefore omits the Pre(...) call:
       0 <= a /\ 1 <= b /\ 0 <= k <= a + b /\ a + b <= 200000. *)
  True.

(* out = None     no valid pair exists, so No is printed
   out = Some q   q is one; any valid pair is accepted *)
Definition Spec (a b k : Z) (out : option (list Z * list Z)) : Prop :=
  (out = None /\ ~exists q, GambitPair a b k q) \/ (exists q, out = Some q /\ GambitPair a b k q).

(* Pair constructor bound for the C-side external name. *)
Definition pair {A B} (x : A) (y : B) : A * B := (x, y).
