(* Codeforces 1201/C - Maximum Median: with at most k unit increments on entries
   of an odd-length array, how large can the median be made. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* m is the median of a: some non-decreasing rearrangement s of a has
   s[|a| / 2] = m, the middle entry of the odd-length array. *)
Definition MedianOf (a : list Z) (m : Z) : Prop :=
  exists s,
    Permutation s a /\ mono_nondec s /\ m = Znth (Zlength a / 2) s 0.

(* median m is attainable within k operations:
     |b| = |a| and a[i] <= b[i] for every i     entries are only increased
     sum(b) - sum(a) <= k                       at most k increments used
     m is the median of b *)
Definition ReachMedian (a : list Z) (k m : Z) : Prop :=
  exists b,
    Zlength b = Zlength a /\
    (forall i, 0 <= i < Zlength a -> Znth i a 0 <= Znth i b 0) /\
    (fold_right Z.add 0) b - (fold_right Z.add 0) a <= k /\
    MedianOf b m.

Definition Pre (k : Z) (a : list Z) : Prop :=
  (* Stated explicitly in the P036 solver Require, so dropped here:
       1 <= Zlength a <= 200000 /\
       Forall (fun x => 1 <= x <= 1000000000) a /\
       1 <= k <= 1000000000   *)
  Z.even (Zlength a) = false.

(* out = max { m : ReachMedian a k m }. *)
Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (ReachMedian a k) (fun x => x) out.
