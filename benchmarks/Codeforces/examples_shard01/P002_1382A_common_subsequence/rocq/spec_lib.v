(* Codeforces 1382/A - Common Subsequence: output a shortest non-empty list that
   is a subsequence of both a and b, or report that none exists. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.IndexedElements.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(a, b : list Z) -> option (list Z).
   Pre: 1 <= |a|, |b| <= 1000 and every entry of a, b lies in [1, 1000]. *)
Definition Pre (a b : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P002 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength a <= 1000 /\ 1 <= Zlength b <= 1000 /\
       Forall (fun x => 1 <= x <= 1000) a /\
       Forall (fun x => 1 <= x <= 1000) b. *)
  True.

(* c is a non-empty common subsequence: c <> [] and c is obtained from each of a
   and b by deleting entries. *)
Definition CommonNonempty (a b c : list Z) : Prop :=
  c <> [] /\ is_subsequence c a /\ is_subsequence c b.

(* out = None            no non-empty common subsequence exists
   out = Some c          c is one of minimal length |c| among them
   Any minimiser is accepted, as the statement allows. *)
Definition Spec (a b : list Z) (out : option (list Z)) : Prop :=
  (out = None /\ ~exists c, CommonNonempty a b c) \/
  (exists c, out = Some c /\ (fun P xs => min_object_of_subset Z.le P (fun ys => Zlength ys) xs) (CommonNonempty a b) c).
