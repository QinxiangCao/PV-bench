(* Codeforces 1725/B - Basketball Together: split candidates into disjoint teams,
   each member's power raised to the team's maximum, and count how many teams can
   beat an enemy of power D. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* wins victories are achievable, via a labelling team_of of the players:
     0 <= team_of(i) <= wins           team 0 means unused, so teams are disjoint
     every team t in 1..wins has a member 'leader' of maximal power mx, and
       #{ i : team_of(i) = t } * mx > D
   the last line being the team's total after every member's power is raised to
   the team maximum mx, which must beat the enemy power D. *)
Definition CanWinTeams (p : list Z) (D wins : Z) : Prop :=
  exists team_of : Z -> Z,
    (forall i, 0 <= i < Zlength p -> 0 <= team_of i <= wins) /\
    (forall t, 1 <= t <= wins ->
      exists mx leader,
        0 <= leader < Zlength p /\ team_of leader = t /\ mx = Znth leader p 0 /\
        (forall i, 0 <= i < Zlength p -> team_of i = t -> Znth i p 0 <= mx) /\
        #(fun i : Z => 0 <= i < Zlength p /\ team_of i = t) * mx > D).

(* Signature: solve_case(D, p : list Z) -> Z. *)
Definition Pre (D : Z) (p : list Z) : Prop :=
  (* Stated explicitly in the P013 solver Require, so dropped here:
       1 <= Zlength p <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) p /\
       1 <= D <= 1000000000   *)
  True.

(* out = max { wins : CanWinTeams p D wins }. *)
Definition Spec (D : Z) (p : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (CanWinTeams p D) (fun x => x) out.
