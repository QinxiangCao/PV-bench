(* Codeforces 1365/C - Rotation Matching: cyclically shift the two permutations
   freely and maximise the number of positions where they agree. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Shifting b by d yields that many agreements:
     0 <= d < |a|
     score = #{ i : a[i] = b[(i + d) mod |a|] }
   Only the relative shift matters, so a single offset d covers every pair of
   rotations of a and b. *)
Definition RotationMatches (a b : list Z) (d score : Z) : Prop :=
  0 <= d < Zlength a /\
  score = #(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 = Znth ((i + d) mod Zlength a) b 0).

(* a and b are both permutations of 1..n; the length bounds are stated in the
   solver Require instead, so they are commented out here. *)
Definition Pre (a b : list Z) : Prop :=
  (* Stated explicitly in the P038 solver Require, so dropped here:
       1 <= Zlength a <= 200000 /\ Zlength b = Zlength a /\ *)
  Permutation a (Zrange 1 (Zlength a + 1)) /\
  Permutation b (Zrange 1 (Zlength b + 1)).

(* out = max { score : some offset d achieves it }. *)
Definition Spec (a b : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (fun v => exists d, RotationMatches a b d v) (fun x => x) out.
