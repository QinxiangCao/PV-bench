(* Codeforces 411/B - Multi-core Processor: cores writing to the same cell in one
   cycle deadlock together with that cell; report for each core the cycle it locks
   up in, or 0. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Core i would lock at cycle t: at t it writes to a cell, ins[i][t-1] <> 0, and
     some core j locked at an earlier cycle u while writing that same cell
       -- the cell is already locked, or
     another core j, still unlocked at t, writes that same cell at t
       -- the two conflict now *)
Definition LockTrigger (ins : list (list Z)) (times : list Z) (i t : Z) : Prop :=
  1 <= t <= Zlength (Znth i ins []) /\ Znth (t - 1) (Znth i ins []) 0 <> 0 /\
  ((exists j u, 0 <= j < Zlength ins /\ 1 <= u < t /\ Znth j times 0 = u /\
      Znth (u - 1) (Znth j ins []) 0 = Znth (t - 1) (Znth i ins []) 0) \/
   (exists j, 0 <= j < Zlength ins /\ j <> i /\ (Znth j times 0 = 0 \/ t <= Znth j times 0) /\
      Znth (t - 1) (Znth j ins []) 0 = Znth (t - 1) (Znth i ins []) 0)).
Definition Pre (k : Z) (ins : list (list Z)) : Prop :=
  (* Stated explicitly in the P049 solver Require, so dropped here:
       1 <= Zlength ins <= 100 /\
       Forall (fun row => Zlength row = m /\ Forall (fun x => 0 <= x <= k) row) ins /\
       1 <= k <= 100   *)
  (* exists m, 1 <= m <= 100. *)
  True.

(* |out| = |ins|, and out[i] is 0 when core i is never triggered, else the
   earliest cycle that triggers it. The condition is mutually recursive --
   LockTrigger reads out itself -- since which cells are locked depends on when
   the other cores locked. *)
Definition Spec (k : Z) (ins : list (list Z)) (out : list Z) : Prop :=
  Zlength out = Zlength ins /\ forall i, 0 <= i < Zlength ins ->
   ((Znth i out 0 = 0 /\ ~exists t, LockTrigger ins out i t) \/
    (1 <= Znth i out 0 /\ LockTrigger ins out i (Znth i out 0) /\
     forall t, 1 <= t < Znth i out 0 -> ~LockTrigger ins out i t)).
