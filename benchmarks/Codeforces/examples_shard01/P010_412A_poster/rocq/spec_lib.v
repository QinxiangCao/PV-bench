(* Codeforces 412/A - Poster: from a ladder standing at square k, print a shortest
   sequence of LEFT / RIGHT / PRINT x actions that paints the whole slogan. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* plan paints the whole slogan, with ladder positions pos[0..|plan|]:
     pos[0] = k                                the ladder starts at square k
     action (d, x) with d = -1 or 1:           a move, pos[j+1] = pos[j] + d, x = 0
     action (0, x):                            a print, pos[j+1] = pos[j]
     1 <= pos[j] <= |s| for every j            the ladder stays on the poster
     for every square i, some print action (0, s[i]) happens at pos[j] = i + 1 *)
Definition ValidPlan (k : Z) (s : list Z) (plan : list (Z * Z)) : Prop :=
  exists pos : list Z,
    Zlength pos = Zlength plan + 1 /\ Znth 0 pos 0 = k /\
    (forall j, 0 <= j < Zlength plan ->
      let ' (d, x) := Znth j plan (0, 0) in
      ((d = - 1 \/ d = 1) /\ Znth (j + 1) pos 0 = Znth j pos 0 + d /\ x = 0 \/
       d = 0 /\ Znth (j + 1) pos 0 = Znth j pos 0)) /\
    (forall j, 0 <= j < Zlength pos -> 1 <= Znth j pos 0 <= Zlength s) /\
    (forall i, 0 <= i < Zlength s -> exists j,
       0 <= j < Zlength plan /\ Znth j plan (0, 0) = (0, Znth i s 0) /\
       Znth j pos 0 = i + 1).

Definition Pre (k : Z) (s : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P010 solver Require, which
     therefore omits the Pre(...) call:
       1 <= k <= Zlength s /\
       1 <= Zlength s <= 100 /\
       Forall (fun c =>
         65 <= c <= 90 \/ 48 <= c <= 57 \/
         c = 46 \/ c = 33 \/ c = 44 \/ c = 63) s. *)
  True.

(* out is a shortest valid plan: it minimises |plan| over ValidPlan k s. Any
   minimiser is accepted, as the statement allows. *)
Definition Spec (k : Z) (s : list Z) (out : list (Z * Z)) : Prop :=
  min_object_of_subset Z.le (ValidPlan k s) (fun ys => Zlength ys) out.

(* The NUL-terminated text an action prints: LEFT, RIGHT, or PRINT x. E.g.
   76, 69, 70, 84, 0 spells 'L','E','F','T'; 32 is the space before x. *)
Definition ActionBytes (action : Z * Z) (bytes : list Z) : Prop :=
  let ' (d, x) := action in
  (d = - 1 /\ x = 0 /\ bytes = [76 ; 69 ; 70 ; 84 ; 0]) \/
  (d = 1 /\ x = 0 /\ bytes = [82 ; 73 ; 71 ; 72 ; 84 ; 0]) \/
  (d = 0 /\ bytes = [80 ; 82 ; 73 ; 78 ; 84 ; 32 ; x ; 0]).

(* One 8-byte output slot after an action is written into it: its bytes, then
   whatever the slot already held past them. *)
Definition ActionSlotBridge
    (action : Z * Z) (before after : list Z) : Prop :=
  Zlength before = 8 /\
  exists bytes,
    ActionBytes action bytes /\
    after = bytes ++ sublist (Zlength bytes) 8 before.

(* The C output buffer of capacity slots:
     ret = |plan|                            the return value is the plan length
     slots 0 .. ret-1 hold the actions' text
     slots ret .. capacity-1 are unchanged *)
Definition SolverOutputBridge
    (capacity : Z) (plan : list (Z * Z)) (ret : Z)
    (before after : list (list Z)) : Prop :=
  ret = Zlength plan /\
  Zlength before = capacity /\ Zlength after = capacity /\
  (forall i, 0 <= i < ret ->
    ActionSlotBridge (Znth i plan (0, 0))
      (Znth i before []) (Znth i after [])) /\
  (forall i, ret <= i < capacity -> Znth i after [] = Znth i before []).
