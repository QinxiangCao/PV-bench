(* Codeforces 433/A - Kitahara Haruki's Gift: can n apples of 100 g and 200 g be
   split, unbroken, into two groups of equal total weight. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(w : list Z) -> Z, with 1 = YES and 0 = NO. *)
Definition Pre (w : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P020 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength w <= 100 /\ Forall (fun x => x = 100 \/ x = 200) w. *)
  True.

(* Some 0/1 vector 'chosen' of length |w| selects a group weighing exactly half
   the total:  2 * sum(chosen[i] * w[i]) = sum(w). *)
Definition FairSplit (w : list Z) : Prop :=
  exists chosen : list Z,
    Zlength chosen = Zlength w /\ Forall (fun b => b = 0 \/ b = 1) chosen /\
    2 * (fold_right Z.add 0) (map (fun q => fst q * snd q) (combine chosen w)) = (fold_right Z.add 0) w.

(* out = 1 for YES, 0 for NO. *)
Definition Spec (w : list Z) (out : Z) : Prop :=
  (out = 1 /\ FairSplit w) \/ (out = 0 /\ ~FairSplit w).

(* C encoding of the verdict: 1 returns 1, 0 returns 0. *)
Definition SolverReturnBridge (out ret : Z) : Prop :=
  (out = 1 /\ ret = 1) \/ (out = 0 /\ ret = 0).
