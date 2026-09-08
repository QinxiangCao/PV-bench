(* Codeforces 753/A - Santa Claus and Candies: hand out all n candies to as many
   children as possible, each child getting a distinct positive amount. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* xs is a legal handout: every xs[i] > 0, the entries are pairwise distinct, and
   sum(xs) = n -- all candies given away. *)
Definition CandyAllocation (n : Z) (xs : list Z) : Prop :=
  Forall (fun x => x > 0) xs /\ NoDup xs /\ (fold_right Z.add 0) xs = n.

(* Signature: solve_case(n) -> list Z.  Pre: 1 <= n <= 1000. *)
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P017 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 1000. *)
  True.

(* out is a legal handout of maximal length |out|. Any maximiser is accepted. *)
Definition Spec (n : Z) (out : list Z) : Prop := max_object_of_subset Z.le (CandyAllocation n) (fun ys => Zlength ys) out.
