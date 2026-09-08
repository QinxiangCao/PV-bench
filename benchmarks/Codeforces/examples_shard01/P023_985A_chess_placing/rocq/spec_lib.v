(* Codeforces 985/A - Chess Placing: on a 1 x n board with n/2 pieces, the least
   number of single-cell moves that brings all pieces onto cells of one colour. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One move: shift a single piece by d = -1 or 1, keeping it inside [1, n] and off
   cells that other pieces occupy. *)
Definition PieceMove (n : Z) (a b : list Z) : Prop :=
  exists i d, 0 <= i < Zlength a /\ (d = - 1 \/ d = 1) /\
    1 <= Znth i a 0 + d <= n /\ ~In (Znth i a 0 + d) a /\
    b = replace_Znth i (Znth i a 0 + d) a.

(* All pieces share a colour: every position even, or every position odd -- the
   board being coloured BWBW... from cell 1. *)
Definition SameColor (p : list Z) : Prop :=
  (Forall (fun x => Z.even x = true) p) \/ (Forall (fun x => Z.even x = false) p).

(* The goal is reachable in exactly 'moves' steps: states[0] = start, each step is
   a PieceMove, and states[moves] is same-coloured. *)
Definition CanPlaceIn (n moves : Z) (start : list Z) : Prop :=
  exists states : list (list Z), Zlength states = moves + 1 /\ Znth 0 states [] = start /\
    (forall i, 0 <= i < moves -> PieceMove n (Znth i states []) (Znth (i + 1) states [])) /\
    SameColor (Znth moves states []).
Definition Pre (n : Z) (p : list Z) : Prop :=
  (* Stated explicitly in the P023 solver Require, so dropped here:
       Zlength p = n / 2 /\
       Forall (fun x => 1 <= x <= n) p /\
       2 <= n <= 100   *)
  Z.even n = true /\
  NoDup p.

(* out = min { d >= 0 : CanPlaceIn n d p }, the fewest moves needed. *)
Definition Spec (n : Z) (p : list Z) (out : Z) : Prop := min_value_of_subset Z.le (fun d => d >= 0 /\ CanPlaceIn n d p) (fun x => x) out.
