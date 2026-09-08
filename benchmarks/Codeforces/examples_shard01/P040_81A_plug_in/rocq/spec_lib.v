(* Codeforces 81/A - Plug-in: repeatedly delete a pair of equal adjacent letters
   until none is left, and print the result. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One deletion: drop positions i and i + 1, which carry equal letters. *)
Definition DeletePair (a b : list Z) : Prop :=
  exists i, 0 <= i < Zlength a - 1 /\ Znth i a 0 = Znth (i + 1) a 0 /\
    b = sublist 0 i a ++ sublist (i + 2) (Zlength a) a.

(* b is a full reduction of a: a chain of deletions leads from a to b, and b
   admits no further deletion. Deletion order does not matter, as the statement
   notes, so b is determined by a. *)
Definition ReducedFrom (a b : list Z) : Prop :=
  exists st : list (list Z), st <> [] /\ Znth 0 st [] = a /\ Znth (Zlength st - 1) st [] = b /\
    (forall i, 0 <= i < Zlength st - 1 -> DeletePair (Znth i st []) (Znth (i + 1) st [])) /\
    ~exists q, DeletePair b q.
Definition Pre (s : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P040 solver Require, which
     therefore omits the Pre(text) call:
       1 <= Zlength s <= 200000 /\ Forall(fun c => 97 <= c <= 122) s. *)
  True.

(* out is the fully reduced string. *)
Definition Spec (s out : list Z) : Prop := ReducedFrom s out.
