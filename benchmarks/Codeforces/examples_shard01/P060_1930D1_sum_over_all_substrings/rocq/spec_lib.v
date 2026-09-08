(* Codeforces 1930/D1 - Sum over all Substrings (Easy Version): sum f over every
   substring of s, where f(p) is the fewest ones in a p-good binary string. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* #{ i : 0 <= i < |xs| and xs[i] = x }, the occurrences of x in xs. *)
Definition Count (x : Z) (xs : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength xs /\ Znth i xs 0 = x).

(* Character c is a mode of the window q[l..r): it occurs there at least
   ceil((r - l) / 2) times, written (r - l + 1) / 2 in integer division.
   Character codes: '0' = 48, '1' = 49. *)
Definition Mode (c : Z) (q : list Z) (l r : Z) : Prop :=
  0 <= l < r /\ r <= Zlength q /\
  Count c (sublist l r q) >= (r - l + 1) / 2.

(* q is p-good: |q| = |p|, q is binary, and for every position i there is a window
   l <= i < r in which p[i] is a mode. *)
Definition PGood (p q : list Z) : Prop :=
  Zlength q = Zlength p /\ Forall (fun c => c = 48 \/ c = 49) q /\
  forall i, 0 <= i < Zlength p -> exists l r, l <= i < r /\ Mode (Znth i p 0) q l r.

(* v = f(p): the least number of ones, Count 49, over all p-good strings q. *)
Definition FValue (p : list Z) (v : Z) : Prop :=
  min_value_of_subset Z.le (fun w => exists q, PGood p q /\ w = Count 49 q) (fun x => x) v.
Definition Pre (s : list Z) : Prop :=
  (* Stated explicitly in the P060 solver Require, so dropped here:
       1 <= Zlength s <= 100 /\
       Forall (fun c => c = 48 \/ c = 49) s  *)
  True.

(* out = sum over 0 <= i < j <= |s| of f(s[i..j)), i.e. f summed over all
   n(n+1)/2 substrings of s. *)
Definition Spec (s : list Z) (out : Z) : Prop :=
  exists f : Z -> Z -> Z,
   (forall i j, 0 <= i < j /\ j <= Zlength s -> FValue (sublist i j s) (f i j)) /\
   out = sum_range 0 (Zlength s - 1) (fun i => sum_range (i + 1) (Zlength s) (fun j => f i j)).
