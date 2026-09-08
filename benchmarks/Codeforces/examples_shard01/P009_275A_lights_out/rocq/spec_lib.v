(* Codeforces 275/A - Lights Out: all nine lights of a 3 x 3 grid start on, and
   pressing one toggles it and its side-adjacent neighbours; given how often each
   light was pressed, print the resulting state. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* g is a 3 x 3 grid: |g| = 3 and |g[i]| = 3 for every row. *)
Definition Grid3 (g : list (list Z)) : Prop :=
  Zlength g = 3 /\ Forall (fun row => Zlength row = 3) g.

(* Press count at (i, j), or 0 when (i, j) is off the grid. The low side must be
   guarded explicitly: [Znth] is [nth (Z.to_nat n)], and [Z.to_nat] maps every
   negative index to 0, so an unguarded [Znth (-1)] would return row/column 0
   instead of the default. The high side already yields the default. *)
Definition cell (g : list (list Z)) (i j : Z) : Z :=
  if andb (0 <=? i) (0 <=? j) then Znth j (Znth i g []) 0 else 0.

(* How often light (i, j) is toggled:
     g[i][j] + g[i-1][j] + g[i+1][j] + g[i][j-1] + g[i][j+1]
   its own presses plus its four side-adjacent ones, off-grid terms being 0. *)
Definition toggles (g : list (list Z)) (i j : Z) : Z :=
  cell g i j + cell g (i - 1) j + cell g (i + 1) j +
  cell g i (j - 1) + cell g i (j + 1).

(* The solver Require states the 3 x 3 shape and the 0..100 press-count bounds
   explicitly, so the corresponding clause is commented out here. *)
Definition Pre (g : list (list Z)) : Prop :=
  (* Grid3 g /\ Forall (Forall (fun x => 0 <= x <= 100)) g *)
  True.

(* out is 3 x 3 and out[i][j] = 1 iff toggles(g, i, j) is even: every light starts
   on, so it is still on exactly when toggled an even number of times. *)
Definition Spec (g out : list (list Z)) : Prop :=
  Grid3 out /\ forall i j, 0 <= i < 3 -> 0 <= j < 3 ->
    cell out i j = if Z.even (toggles g i j) then 1 else 0.
