(* Codeforces 705/B - Spider Man: cycles are repeatedly split in two and the
   player unable to move loses; after each added cycle, say who wins the game on
   the cycles added so far. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One move: replace some cycle a[i] = x >= 2 by two cycles of p and x - p
   vertices, 1 <= p < x. The result is compared up to Permutation, the set of
   cycles being a multiset. *)
Definition SplitMove (a b : list Z) : Prop :=
  exists i p x, 0 <= i < Zlength a /\ x = Znth i a 0 /\ 1 <= p < x /\
    Permutation b (p :: (x - p) :: sublist 0 i a ++ sublist (i + 1) (Zlength a) a).

(* A complete play from init:
     p[0] = init
     p[i] -> p[i+1] by one SplitMove
     every state but the last still contains a cycle of >= 2 vertices
     the last state is all 1s, so no move remains *)
Definition SplitPlay (init : list Z) (p : list (list Z)) : Prop :=
  p <> [] /\ Znth 0 p [] = init /\
  (forall i, 0 <= i < Zlength p - 1 -> SplitMove (Znth i p []) (Znth (i + 1) p [])) /\
  Forall (fun x => x = 1) (Znth (Zlength p - 1) p []) /\
  (forall i, 0 <= i < Zlength p - 1 -> exists x, In x (Znth i p []) /\ x >= 2).

(* The play p obeys strategy f at the first player's turns, i.e. at the moves
   made from even-indexed states, the first player moving first. *)
Definition SplitFirstFollows (f : list (list Z) -> list Z) (p : list (list Z)) : Prop :=
  forall i, 0 <= i < Zlength p - 1 -> Z.even i = true ->
    Znth (i + 1) p [] = f (sublist 0 (i + 1) p).

(* The first player has a winning strategy f:
     f is a legal move at every position that has one
     every play following f has |p| even, hence |p| - 1 moves, an odd number
   so the last move is the first player's and the second player is left stuck. *)
Definition SplitFirstWins (a : list Z) : Prop :=
  exists f, (forall hist, hist <> [] -> (exists x, In x (Znth (Zlength hist - 1) hist []) /\ x >= 2) ->
    SplitMove (Znth (Zlength hist - 1) hist []) (f hist)) /\
  forall p, SplitPlay a p -> SplitFirstFollows f p -> Z.even (Zlength p) = true.

(* 1 <= |added| <= 10^5 and every added[i] in [1, 10^9]. *)
Definition Pre (added : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P022 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength added <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) added. *)
  True.

(* One verdict per test: |out| = |added| and out[i] = 1 if the first player wins
   on the multiset added[0..i], else out[i] = 2. *)
Definition Spec (added out : list Z) : Prop :=
  Zlength out = Zlength added /\ forall i, 0 <= i < Zlength added ->
    ((Znth i out 0 = 1 /\ SplitFirstWins (sublist 0 (i + 1) added)) \/
     (Znth i out 0 = 2 /\ ~SplitFirstWins (sublist 0 (i + 1) added))).
