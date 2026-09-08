(* Codeforces 1313/A - Fast Food Restaurant: with a, b, c portions of the three
   dishes, how many visitors can be served pairwise different non-empty sets of
   dishes, one portion of each dish per visitor. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Menu kinds 1..7 are the seven non-empty dish sets A, B, C, AB, AC, BC, ABC;
   UsesA / UsesB / UsesC say which of them contain each dish. *)
Definition UsesA (kind : Z) : Prop := kind = 1 \/ kind = 4 \/ kind = 5 \/ kind = 7.
Definition UsesB (kind : Z) : Prop := kind = 2 \/ kind = 4 \/ kind = 6 \/ kind = 7.
Definition UsesC (kind : Z) : Prop := kind = 3 \/ kind = 5 \/ kind = 6 \/ kind = 7.

(* guests visitors can be served:
     exists chosen : Z -> Prop                    a set of menu kinds
     #{ kind in 1..7 : chosen kind } = guests      one visitor per chosen kind
     #{ chosen kinds using A } <= a                dish A stock
     #{ chosen kinds using B } <= b                dish B stock
     #{ chosen kinds using C } <= c                dish C stock
   Distinct visitors get distinct sets automatically: a kind is chosen or not. *)
Definition Feeds (a b c guests : Z) : Prop :=
  exists chosen : Z -> Prop,
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind) = guests /\
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesA kind) <= a /\
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesB kind) <= b /\
    #(fun kind : Z => 1 <= kind < 8 /\ chosen kind /\ UsesC kind) <= c.

(* 0 <= a, b, c <= 10. *)
Definition Pre (a b c : Z) : Prop :=
  (* Stated explicitly in the P007 solver Require, which therefore omits the
     Pre(...) call: 0 <= a <= 10 /\ 0 <= b <= 10 /\ 0 <= c <= 10. *)
  True.

(* out = max { guests : Feeds a b c guests }, the largest number of visitors. *)
Definition Spec (a b c out : Z) : Prop := max_value_of_subset Z.le (Feeds a b c) (fun x => x) out.
