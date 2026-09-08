(* Codeforces 623/B - Array GCD: at most one segment removal, paying del per
   element, and at most a change of 1 per remaining element, paying 'change' each;
   reach a gcd above 1 as cheaply as possible. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* #{ i : 0 <= i < |xs| and xs[i] = x }, the occurrences of x in xs. *)
Definition Count (x : Z) (xs : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength xs /\ Znth i xs 0 = x).

(* d = gcd(xs) for a non-empty xs, and d > 0. *)
Definition IsPositiveGcd (d : Z) (xs : list Z) : Prop :=
  d > 0 /\ xs <> [] /\ d = fold_right Z.gcd 0 xs.

(* What is left after removing one segment: a proper part of the array may go,
   never all of it. *)
Definition KeptAfterRemoval (a : list Z) (l r : Z) (kept : list Z) : Prop :=
  0 <= l <= r /\ r <= Zlength a /\ r - l < Zlength a /\
  kept = sublist 0 l a ++ sublist r (Zlength a) a.

(* Every remaining element may move by at most one. *)
Definition Adjusted (kept delta result : list Z) : Prop :=
  Zlength delta = Zlength kept /\
  Forall (fun d => d = (- 1) \/ d = 0 \/ d = 1) delta /\
  result = map (fun q => fst q + snd q) (combine kept delta).

(* The coins paid: one price per removed element, another per element moved. *)
Definition ChangeCost (del change l r : Z) (delta : list Z) : Z :=
  (r - l) * del + Count (- 1) delta * change + Count 1 delta * change.

(* A way of reaching an array whose greatest common divisor exceeds one, and
   what it costs. *)
Definition GCDChange (a : list Z) (del change cost : Z) : Prop :=
  exists (l r : Z) (kept delta result : list Z),
    KeptAfterRemoval a l r kept /\
    Adjusted kept delta result /\
    (exists g, g > 1 /\ IsPositiveGcd g result) /\
    cost = ChangeCost del change l r delta.
Definition Pre (del change : Z) (a : list Z) : Prop :=
  (* Stated explicitly in the P082 solver Require, so dropped here:
       1 <= Zlength a <= 1000000 /\
       Forall (fun x => 2 <= x <= 1000000000) a /\
       0 <= del <= 1000000000 /\
       0 <= change <= 1000000000  *)
  True.

(* out = min { cost : GCDChange a del change cost }. *)
Definition Spec (del change : Z) (a : list Z) (out : Z) : Prop := min_value_of_subset Z.le (GCDChange a del change) (fun x => x) out.
