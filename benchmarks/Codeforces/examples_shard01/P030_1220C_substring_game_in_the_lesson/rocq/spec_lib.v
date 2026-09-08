(* Codeforces 1220/C - Substring Game in the Lesson: from the window l = r = k,
   players alternately widen it to a lexicographically smaller substring, Ann
   first; for every k say who wins. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

(* a is lexicographically smaller than b: they first differ at an index where a's
   character is smaller, or a is a strict prefix of b. *)
Definition LexLt (a b : list Z) : Prop :=
  (exists i, 0 <= i < Z.min (Zlength a) (Zlength b) /\
    (forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0) /\
    Znth i a 0 < Znth i b 0) \/
  (Zlength a < Zlength b /\ is_prefix a b).

(* One move from window (l, r) to (l', r'):
     l' <= l and r' >= r          the window only widens
     0 <= l' <= r' < |s|          and stays inside the string
     s[l'..r'] < s[l..r]          lexicographically smaller substring *)
Definition IntervalMove (s : list Z) (a b : Z * Z) : Prop :=
  fst b <= fst a /\ snd a <= snd b /\ 0 <= fst b <= snd b /\ snd b < Zlength s /\
  LexLt (sublist (fst b) (snd b + 1) s) (sublist (fst a) (snd a + 1) s).

(* A complete play from k:
     p[0] = (k, k)
     p[i] -> p[i+1] by one IntervalMove
     the last window admits no move, so the player to move there has lost
   L7 representation note: IntervalPlay is a game history, not mere reachability:
   its ordered intermediate states are observed by AnnFollows and its length
   parity determines the winner. A transitive closure would erase both facts. *)
Definition IntervalPlay (s : list Z) (k : Z) (p : list (Z * Z)) : Prop :=
  p <> [] /\
  Znth 0 p (0, 0) = (k, k) /\
  (forall i, 0 <= i < Zlength p - 1 ->
    IntervalMove s (Znth i p (0, 0)) (Znth (i + 1) p (0, 0))) /\
  ~exists q, IntervalMove s (Znth (Zlength p - 1) p (0, 0)) q.

(* The play p obeys Ann's strategy f at her turns, i.e. at the moves made from
   even-indexed windows, Ann moving first. *)
Definition AnnFollows (f : list (Z * Z) -> Z * Z) (p : list (Z * Z)) : Prop :=
  forall i, 0 <= i < Zlength p - 1 -> Z.even i = true ->
    Znth (i + 1) p (0, 0) = f (sublist 0 (i + 1) p).

(* Ann has a winning strategy f:
     f is a legal move at every window that has one
     every play following f has |p| even, hence |p| - 1 moves, an odd number
   so the last move is Ann's and Mike is left stuck. *)
Definition AnnWins (s : list Z) (k : Z) : Prop :=
  exists f,
    (forall hist, hist <> [] ->
      (exists q, IntervalMove s (Znth (Zlength hist - 1) hist (0, 0)) q) ->
      IntervalMove s (Znth (Zlength hist - 1) hist (0, 0)) (f hist)) /\
    forall p, IntervalPlay s k p -> AnnFollows f p -> Z.even (Zlength p) = true.

(* 1 <= |s| <= 5 * 10^5 and every s[i] a lowercase letter, code 97 to 122. *)
Definition Pre (s : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P030 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength s <= 500000 /\
       Forall (fun c => 97 <= c <= 122) s. *)
  True.

(* One verdict per starting position: |out| = |s| and out[k] = 1 when Ann wins
   the game with this s and k, 0 when Mike does. *)
Definition Spec (s : list Z) (out : list Z) : Prop :=
  Zlength out = Zlength s /\
  forall k, 0 <= k < Zlength s ->
    ((Znth k out 0 = 1 /\ AnnWins s k) \/ (Znth k out 0 = 0 /\ ~AnnWins s k)).
