(* Codeforces 1607/E - Robot on the Board 1: choose the starting cell of an n x m
   board from which the robot executes as many of the commands as possible before
   it would leave the board. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Displacement of a command as (row, column): 'L' = 76 gives (0, -1), 'R' = 82
   gives (0, 1), 'U' = 85 gives (-1, 0), and otherwise 'D' gives (1, 0). *)
Definition Delta (c : Z) : Z * Z :=
  if Z.eqb c 76 then (0, - 1) else if Z.eqb c 82 then (0, 1)
  else if Z.eqb c 85 then (- 1, 0) else (1, 0).

(* From cell 'start' the robot survives its first q commands: for every prefix
   length p <= q, start plus the sum of the first p displacements is still on the
   board, row in [1, n] and column in [1, m]. *)
Definition Executes (n m : Z) (s : list Z) (start : Z * Z) (q : Z) : Prop :=
  0 <= q <= Zlength s /\ forall p, 0 <= p <= q ->
  let ds := map Delta (sublist 0 p s) in
  1 <= fst start + (fold_right Z.add 0) (map fst ds) <= n /\ 1 <= snd start + (fold_right Z.add 0) (map snd ds) <= m.
Definition Pre (n m : Z) (s : list Z) : Prop :=
  (* Stated explicitly in the P048 solver Require, so dropped here:
       1 <= Zlength s <= 1000000 /\
       Forall (fun c => c = 76 \/ c = 82 \/ c = 68 \/ c = 85) s /\
       1 <= n <= 1000000 /\
       1 <= m <= 1000000   *)
  True.

(* out is a cell of the board that survives a maximal number of commands: some q
   is survivable from out and no starting cell survives more. Any optimal cell is
   accepted. *)
Definition Spec (n m : Z) (s : list Z) (out : Z * Z) : Prop :=
  1 <= fst out <= n /\ 1 <= snd out <= m /\ exists q,
  Executes n m s out q /\
  max_value_of_subset Z.le
    (fun q' => exists st, 1 <= fst st <= n /\ 1 <= snd st <= m /\ Executes n m s st q')
    (fun x => x) q.
