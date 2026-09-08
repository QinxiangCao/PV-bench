(* Codeforces 1538/F - Interesting Function: total number of digits that change
   while incrementing l one at a time up to r. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* d is the decimal representation of x: non-empty, d[0] <> 0, digits in [0, 9],
   most-significant first. *)
Definition DecimalRep (x : Z) (d : list Z) : Prop :=
  d <> [] /\ Znth 0 d 0 <> 0 /\ Forall (fun z => 0 <= z <= 9) d /\
  fold_left (fun a z => 10 * a + z) d 0 = x.

(* c is how many digits change when x becomes x + 1: with the two representations
   right-aligned to the common length L = max(|a|, |b|),
     c = #{ i : 0 <= i < L and the two numerals differ at i }
   so a newly gained leading digit counts as changed. *)
Definition ChangedDigits (x c : Z) : Prop :=
  exists a b L, DecimalRep x a /\ DecimalRep (x + 1) b /\ L = Z.max (Zlength a) (Zlength b) /\
    c = #(fun i : Z => 0 <= i < L /\
      Znth (i - (L - Zlength a)) a 0 <> Znth (i - (L - Zlength b)) b 0).
Definition Pre (l r : Z) : Prop :=
  (* Every clause below is stated explicitly in the P041 solver Require, which
     therefore omits the Pre(l, r) call:
       1<=l<r /\ r<=1000000000. *)
  True.

(* out = sum over x in [l, r-1] of ChangedDigits(x), one term per increment. *)
Definition Spec (l r out : Z) : Prop :=
  exists f, (forall x, l <= x < r -> ChangedDigits x (f x)) /\ out = sum_range l (r - 1) f.
