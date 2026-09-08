(* Codeforces 639/D - Bear and Contribution: an upvoted blog costs b minutes and
   adds 5, a comment costs c and adds 1; least time to make at least k users share
   one contribution value. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Cheapest way to lift one user from 'from' to 'target':
     cost = min { blogs * b + comments * c :  blogs, comments >= 0  and
                  target = from + 5 * blogs + comments }
   Unreachable targets, target < from, admit no such pair at all. *)
Definition RaiseCost (b c from target cost : Z) : Prop :=
  min_value_of_subset Z.le (fun v => exists blogs comments, blogs >= 0 /\ comments >= 0 /\
 target = from + 5 * blogs + comments /\ v = blogs * b + comments * c) (fun x => x) cost.

(* The k bloggers whose contributions are raised to one common value. *)
Definition ChosenBloggers (values : list Z) (k : Z) (chosen : list Z) : Prop :=
  Zlength chosen = k /\ NoDup chosen /\
  Forall (fun i => 0 <= i < Zlength values) chosen.

(* What bringing them to a common target costs altogether. *)
Definition TieCost (values : list Z) (k b c cost : Z) : Prop :=
  exists (chosen costs : list Z) (target : Z),
    ChosenBloggers values k chosen /\ Zlength costs = k /\
    (forall i, 0 <= i < k ->
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) /\
    cost = fold_right Z.add 0 costs.
Definition Pre (k b c : Z) (values : list Z) : Prop :=
  (* Stated explicitly in the P086 solver Require, so dropped here:
       Zlength values <= 200000 /\
       Forall (fun x => - 1000000000 <= x <= 1000000000) values /\
       2 <= k <= Zlength values /\
       1 <= b <= 1000 /\
       1 <= c <= 1000  *)
  True.

(* out = min { cost : TieCost values k b c cost }. *)
Definition Spec (k b c : Z) (values : list Z) (out : Z) : Prop := min_value_of_subset Z.le (TieCost values k b c) (fun x => x) out.
