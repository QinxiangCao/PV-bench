(* Codeforces 1474/D - Cleaning: an operation removes one stone from each of two
   neighbouring non-empty piles; decide whether all stones can be removed, given
   at most one preliminary swap of neighbours. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One operation: pick neighbouring piles i, i+1 that are both non-empty and lower
   each by 1. *)
Definition CleanStep (a b : list Z) : Prop :=
  exists i, 0 <= i < Zlength a - 1 /\ Znth i a 0 > 0 /\ Znth (i + 1) a 0 > 0 /\
  b = replace_Znth (i + 1) (Znth (i + 1) a 0 - 1) (replace_Znth i (Znth i a 0 - 1) a).

(* All stones can be removed:
     base = a, or a with one neighbouring pair swapped   the superability, used
                                                         at most once
     a chain of CleanSteps from base ...
     ... ends with every pile empty *)
Definition Cleanable (a : list Z) : Prop :=
  exists (base : list Z) (st : list (list Z)),
   (base = a \/ exists i, 0 <= i < Zlength a - 1 /\
      base = replace_Znth (i + 1) (Znth i a 0) (replace_Znth i (Znth (i + 1) a 0) a)) /\
   st <> [] /\ Znth 0 st [] = base /\ Forall (fun x => x = 0) (Znth (Zlength st - 1) st []) /\
   forall q, 0 <= q < Zlength st - 1 -> CleanStep (Znth q st []) (Znth (q + 1) st []).
Definition Pre (a : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P075 solver Require, which
     therefore omits the Pre(...) call:
       2 <= Zlength a <= 200000 /\ Forall(fun x => 1 <= x <= 1000000000)a. *)
  True.

(* out = 1 for YES, 0 for NO. *)
Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 1 /\ Cleanable a) \/ (out = 0 /\ ~Cleanable a).
