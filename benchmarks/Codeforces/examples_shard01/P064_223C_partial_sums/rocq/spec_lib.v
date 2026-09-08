(* Codeforces 223/C - Partial Sums: apply the prefix-sum operation modulo 10^9+7
   exactly k times and print the resulting array. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One operation: |b| = |a| and b[i] = (a[0] + ... + a[i]) mod (10^9 + 7). *)
Definition PrefixStep (a b : list Z) : Prop :=
  Zlength b = Zlength a /\ forall i, 0 <= i < Zlength a ->
  Znth i b 0 = (sum_range 0 i (fun j => Znth j a 0)) mod 1000000007.

(* b is a after exactly k operations: st[0] = a, st[k] = b, and each st[i] ->
   st[i+1] is one PrefixStep. *)
Definition IteratePrefix (a b : list Z) (k : Z) : Prop :=
  exists st : list (list Z), Zlength st = k + 1 /\ Znth 0 st [] = a /\ Znth k st [] = b /\
    forall i, 0 <= i < k -> PrefixStep (Znth i st []) (Znth (i + 1) st []).
Definition Pre (k : Z) (a : list Z) : Prop :=
  (* Stated explicitly in the P064 solver Require, so dropped here:
       1 <= Zlength a <= 2000 /\
       Forall (fun x => 0 <= x <= 1000000000) a /\
       0 <= k <= 1000000000  *)
  True.

(* out is a after k operations. *)
Definition Spec (k : Z) (a out : list Z) : Prop := IteratePrefix a out k.
