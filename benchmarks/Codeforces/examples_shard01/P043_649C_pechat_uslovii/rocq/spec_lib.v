(* Codeforces 649/C - Printing the Statements: x sheets take two pages each and y
   sheets take one, and no sheet may mix two teams' pages; maximise how many teams
   get their whole set printed. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* 'teams' sets can be printed in full, via a 0/1 choice vector and per-team sheet
   counts doubles[i], singles[i] >= 0:
     sum(chosen) = teams
     sum(doubles) <= x,  sum(singles) <= y     the two paper stocks
     chosen[i] = 1  ->  2 * doubles[i] + singles[i] >= pages[i]
     chosen[i] = 0  ->  doubles[i] = singles[i] = 0
   the per-team counts making sure no sheet is shared between two teams. *)
Definition CanPrint (pages : list Z) (x y teams : Z) : Prop :=
  exists chosen doubles singles : list Z,
    Zlength chosen = Zlength pages /\ Zlength doubles = Zlength pages /\ Zlength singles = Zlength pages /\
    Forall (fun z => z = 0 \/ z = 1) chosen /\ Forall (fun z => z >= 0) doubles /\ Forall (fun z => z >= 0) singles /\
    (fold_right Z.add 0) chosen = teams /\ (fold_right Z.add 0) doubles <= x /\ (fold_right Z.add 0) singles <= y /\
    (forall i, 0 <= i < Zlength pages ->
      (Znth i chosen 0 = 1 -> 2 * Znth i doubles 0 + Znth i singles 0 >= Znth i pages 0) /\
      (Znth i chosen 0 = 0 -> Znth i doubles 0 = 0 /\ Znth i singles 0 = 0)).
Definition Pre (pages : list Z) (x y : Z) : Prop :=
  (* Stated explicitly in the P043 solver Require, so dropped here:
       1 <= Zlength pages <= 200000 /\
       Forall (fun p => 1 <= p <= 10000) pages /\
       x >= 0 /\
       y >= 0   *)
  True.

(* out = max { teams : CanPrint pages x y teams }. *)
Definition Spec (pages : list Z) (x y out : Z) : Prop := max_value_of_subset Z.le (CanPrint pages x y) (fun x => x) out.
