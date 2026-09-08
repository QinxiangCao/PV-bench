(* Codeforces 535/C - Tavas and Karafs: heights are s_i = A + (i-1)B, and an
   m-bite lowers at most m distinct uneaten karafses by 1; per query (l, t, m)
   report the largest r whose range l..r can be eaten in at most t bites. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One m-bite: pick at most m distinct positions of positive height and lower each
   of them by 1, leaving the rest untouched. *)
Definition BiteStep (m : Z) (a b : list Z) : Prop :=
  exists chosen : list Z, NoDup chosen /\ Zlength chosen <= m /\ (Forall (fun i => 0 <= i < (Zlength a)) chosen) /\
  Forall (fun i => Znth i a 0 > 0) chosen /\ Zlength b = Zlength a /\
  forall i, 0 <= i < Zlength a -> Znth i b 0 = if existsb (Z.eqb i) chosen then Znth i a 0 - 1 else Znth i a 0.

(* The karafses s_l .. s_r can be eaten within t bites:
     l <= r
     the start state is [A + (l-1)B, ..., A + (r-1)B]
     at most t BiteSteps are taken, |st| <= t + 1
     the final state is all zeros *)
Definition Eatable (A B l t m r : Z) : Prop :=
  l <= r /\ exists st : list (list Z), 1 <= Zlength st <= t + 1 /\
  Znth 0 st [] = map (fun i => A + (l + i - 1) * B) (Zrange 0 (r - l + 1)) /\
  (forall q, 0 <= q < Zlength st - 1 -> BiteStep m (Znth q st []) (Znth (q + 1) st [])) /\
  Forall (fun x => x = 0) (Znth (Zlength st - 1) st []).

(* The answer to one query (l, t, m):
     ans = -1     not even the single karafs s_l can be eaten
     otherwise    ans >= l is eatable and ans + 1 is not, i.e. the largest r *)
Definition QueryAnswer (A B : Z) (q : Z * Z * Z) (ans : Z) : Prop :=
  let ' (l, t, m) := q in
  (ans = (- 1) /\ ~Eatable A B l t m l) \/
  (ans >= l /\ Eatable A B l t m ans /\ ~Eatable A B l t m (ans + 1)).
Definition Pre (A B : Z) (queries : list (Z * Z * Z)) : Prop :=
  (* Stated explicitly in the P065 solver Require, so dropped here:
       1 <= Zlength queries <= 100000 /\
       Forall (fun q => let ' (l, t, m) := q in 1 <= l <= 1000000 /\ 1 <= t <= 1000000 /\ 1 <= m <= 1000000) queries /\
       1 <= A <= 1000000 /\
       1 <= B <= 1000000  *)
  True.

(* One answer per query: |out| = |queries| and out[i] is the QueryAnswer for
   queries[i]. *)
Definition Spec (A B : Z) (queries : list (Z * Z * Z)) (out : list Z) : Prop :=
  Zlength out = Zlength queries /\ forall i, 0 <= i < Zlength queries ->
  QueryAnswer A B (Znth i queries (0, 0, 0)) (Znth i out 0).
