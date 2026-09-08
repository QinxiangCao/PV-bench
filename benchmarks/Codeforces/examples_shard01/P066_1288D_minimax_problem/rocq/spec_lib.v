(* Codeforces 1288/D - Minimax Problem: choose rows i and j, possibly equal, so
   that the smallest column-wise maximum of the two is as large as possible. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The row two chosen rows combine into: each column keeps the larger value. *)
Definition CombinedEntry (rows : list (list Z)) (i j c : Z) : Z :=
  Z.max (Znth c (Znth i rows []) 0) (Znth c (Znth j rows []) 0).

(* What a pair of rows scores: the smallest entry of the combined row. *)
Definition PairScore (rows : list (list Z)) (i j score : Z) : Prop :=
  0 <= i < Zlength rows /\ 0 <= j < Zlength rows /\
  min_value_of_subset Z.le
    (fun v => exists c, 0 <= c < Zlength (Znth i rows []) /\
                v = CombinedEntry rows i j c)
    (fun x => x) score.
Definition Pre (rows : list (list Z)) : Prop :=
  (* Stated explicitly in the P066 solver Require, so dropped here:
       1 <= Zlength rows <= 300000  *)
  exists m, 1 <= m <= 8 /\
  Forall (fun row => Zlength row = m) rows
  (* Element bounds are stated explicitly in both solver and feasible Require. *)
  (* /\ Forall (Forall (fun x => 0 <= x <= 1000000000)) rows *)
  .

Definition MatrixEntriesBounded (rows : list (list Z)) : Prop :=
  Forall (Forall (fun x => 0 <= x <= 1000000000)) rows.

(* out = (i, j), 1-based, is an optimal pair: its PairScore 'best' is the maximum
   of PairScore over all pairs of rows. Any optimal pair is accepted. *)
Definition Spec (rows : list (list Z)) (out : Z * Z) : Prop :=
  exists best, PairScore rows (fst out - 1) (snd out - 1) best /\
  max_value_of_subset Z.le
    (fun v => exists i j, PairScore rows i j v)
    (fun x => x) best.
