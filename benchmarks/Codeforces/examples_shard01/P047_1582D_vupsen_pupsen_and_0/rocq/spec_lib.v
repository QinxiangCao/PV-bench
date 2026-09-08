(* Codeforces 1582/D - Vupsen, Pupsen and 0: given a with no zero entry, print a
   zero-free b of the same length that is orthogonal to it. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P047 solver Require, so dropped here:
       2 <= Zlength a <= 100000 /\
       Forall (fun x => - 10000 <= x <= 10000 /\ x <> 0) a  *)
  True.

(* out is an acceptable b:
     |out| = |a|
     out[i] <> 0 for every i
     sum(a[i] * out[i]) = 0            orthogonal to a
     sum(|out[i]|) <= 10^9             the size bound
   Any such b is accepted. *)
Definition Spec (a out : list Z) : Prop :=
  Zlength out = Zlength a /\ Forall (fun x => x <> 0) out /\
  (fold_right Z.add 0) (map (fun q => fst q * snd q) (combine a out)) = 0 /\
  (fold_right Z.add 0) (map Z.abs out) <= 1000000000.
