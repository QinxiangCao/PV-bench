(* Codeforces 1316/E - Team Building: pick one player for each of the p positions
   and k audience members, all distinct people, maximising the total strength. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* score is attainable by some selection:
     |players| = p, one person per position; |audience| = k
     the players and audience indices are all distinct people
     score = sum over positions j of skill[players[j]][j]
             + sum over i in audience of aud[i] *)
Definition TeamChoice (aud : list Z) (skill : list (list Z)) (k : Z) (score : Z) : Prop :=
  exists players audience : list Z,
   Zlength players = Zlength (Znth 0 skill []) /\ Zlength audience = k /\
   NoDup (players ++ audience) /\ (Forall (fun i => 0 <= i < (Zlength aud)) (players ++ audience)) /\
   score = (fold_right Z.add 0) (map (fun q => Znth (fst q) (Znth (snd q) skill []) 0)
      (combine (Zrange 0 (Zlength players)) players)) +
     (fold_right Z.add 0) (map (fun i => Znth i aud 0) audience).
Definition Pre (k : Z) (aud : list Z) (skill : list (list Z)) : Prop :=
  (* Stated explicitly in the P080 solver Require, so dropped here:
       2 <= Zlength aud <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) aud /\
       1 <= k /\
       1 <= p <= 7 /\
       Forall (Forall (fun x => 1 <= x <= 1000000000)) skill *)
  Zlength skill = Zlength aud /\
  exists p,
  p + k <= Zlength aud /\
  Zlength skill = Zlength aud /\
  Forall (fun row => Zlength row = p) skill.

(* out = max { score : TeamChoice aud skill k score }. *)
Definition Spec (k : Z) (aud : list Z) (skill : list (list Z)) (out : Z) : Prop :=
  (max_value_of_subset Z.le (TeamChoice aud skill k) (fun x => x)) out.
