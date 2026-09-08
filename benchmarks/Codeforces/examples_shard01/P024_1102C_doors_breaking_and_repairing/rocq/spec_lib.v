(* Codeforces 1102/C - Doors Breaking and Repairing: with both sides playing
   optimally, how many doors end at durability 0. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* If the attack is stronger than the repair, every door can eventually be
   destroyed.  Otherwise only doors whose initial durability is at most x can
   be destroyed, and optimal repair saves every second such door. *)
Definition WeakDoorCount (x : Z) (a : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 <= x).

Definition Pre (x y : Z) (a : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P024 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength a <= 100 /\
       1 <= x <= 100000 /\ 1 <= y <= 100000 /\
       Forall (fun z => 1 <= z <= 100000) a. *)
  True.

(* out = |a|                          when y < x, every door eventually falls
   out = (w + 1) / 2 = ceil(w / 2)    otherwise, where w = WeakDoorCount x a,
   the number of doors of durability <= x, of which optimal repair saves every
   second one. *)
Definition Spec (x y : Z) (a : list Z) (out : Z) : Prop :=
  out = if Z.ltb y x then Zlength a else (WeakDoorCount x a + 1) / 2.
