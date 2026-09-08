(* Codeforces 1384/A - Common Prefixes: given a_1..a_n, output n+1 lowercase
   strings whose consecutive longest common prefixes have exactly those lengths. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The statement's own notion: the longest k for which the first k characters
   of the two strings agree. *)
Definition LCP (a b : list Z) (k : Z) : Prop :=
  max_value_of_subset Z.le
    (fun j => 0 <= j <= Z.min (Zlength a) (Zlength b) /\
              forall i, 0 <= i < j -> Znth i a 0 = Znth i b 0)
    (fun x => x) k.

(* Signature: solve_case(a : list Z) -> list (list Z), one string per line. *)
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P025 solver Require, so dropped here:
       1 <= Zlength a <= 100 /\
       Forall (fun x => 0 <= x <= 50) a  *)
  True.

(* What the output format accepts as one printed string. *)
Definition ValidAnswerString (s : list Z) : Prop :=
  1 <= Zlength s <= 200 /\ Forall (fun c => 97 <= c <= 122) s.

(* out is an acceptable family of strings:
     |out| = |a| + 1
     every out[i] is printable, 1 <= |out[i]| <= 200 lowercase letters
     LCP(out[i], out[i+1]) = a[i] for every i
   Any such family is accepted. *)
Definition Spec (a : list Z) (out : list (list Z)) : Prop :=
  Zlength out = Zlength a + 1 /\
  Forall ValidAnswerString out /\
  forall i, 0 <= i < Zlength a ->
    LCP (Znth i out []) (Znth (i + 1) out []) (Znth i a 0).
