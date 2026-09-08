(* Codeforces 1382/B - Sequential Nim: players alternately take stones from the
   first non-empty pile; decide who wins under optimal play. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* k counts the leading one-stone piles: piles[i] = 1 for all i < k, and either
   k = |piles| or piles[k] <> 1. *)
Definition LeadingOnes (piles : list Z) (k : Z) : Prop :=
  0 <= k <= Zlength piles /\
  (forall i, 0 <= i < k -> Znth i piles 0 = 1) /\
  (k = Zlength piles \/ Znth k piles 0 <> 1).

(* With k leading one-stone piles, the first player wins exactly when
     k = |piles| and k is odd        every pile is a single stone
     k < |piles| and k is even       the first big pile is reached by player one
   since the leading single-stone piles force alternating forced moves. *)
Definition FirstWins (piles : list Z) : Prop :=
  exists k, LeadingOnes piles k /\
    ((k = Zlength piles /\ Z.even k = false) \/
     (k < Zlength piles /\ Z.even k = true)).

(* Every clause below is stated explicitly in the P018 solver Require, which
   therefore omits the Pre(...) call. *)
Definition Pre (piles : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P018 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength piles <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) piles. *)
  True.

(* out = 1 for First, 0 for Second. *)
Definition Spec (piles : list Z) (out : Z) : Prop :=
  (out = 1 /\ FirstWins piles) \/ (out = 0 /\ ~FirstWins piles).

(* C encoding of the verdict: 1 returns 1, 0 returns 0. *)
Definition SolverReturnBridge (out ret : Z) : Prop :=
  (out = 1 /\ ret = 1) \/ (out = 0 /\ ret = 0).
