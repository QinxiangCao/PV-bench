(* Codeforces 371/A - K-Periodic Array: fewest entries of a 1/2-valued array that
   must change to make it k-periodic. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* a has period k: k | |a| and a[i] = a[i+k] whenever both positions exist. *)
Definition KPeriodic (k : Z) (a : list Z) : Prop :=
  (k | Zlength a) /\ forall i, 0 <= i < Zlength a - k -> Znth i a 0 = Znth (i + k) a 0.

(* Hamming distance: #{ i : 0 <= i < |a| and a[i] <> b[i] }. *)
Definition DifferenceCount (a b : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 <> Znth i b 0).

(* k | |a|; the bounds 1 <= k <= |a| and |a| <= 100 and the 1/2-valuedness
   of a are stated in the solver Require instead, so they are commented out here. *)
Definition Pre (k : Z) (a : list Z) : Prop :=
  (* 1 <= k <= Zlength a /\ *)
  (* Zlength a <= 100 /\  *)
  (k | Zlength a)
  (* /\ Forall (fun x => x = 1 \/ x = 2) a *)
  .

(* out = min { DifferenceCount a b : |b| = |a|, b is 1/2-valued, b is k-periodic }
   -- the fewest entries of a that must change. *)
Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (fun d => exists b, Zlength b = Zlength a /\
 Forall (fun x => x = 1 \/ x = 2) b /\ KPeriodic k b /\ d = DifferenceCount a b) (fun x => x) out.
