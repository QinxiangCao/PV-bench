Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.

Definition zquad_1 (q : Z * Z * Z * Z) : Z :=
  fst (fst (fst q)).

Definition zquad_2 (q : Z * Z * Z * Z) : Z :=
  snd (fst (fst q)).

Definition zquad_3 (q : Z * Z * Z * Z) : Z :=
  snd (fst q).

Definition zquad_4 (q : Z * Z * Z * Z) : Z :=
  snd q.

Definition MatrixCell (matrix : list Z) (n i j : Z) : Z :=
  Znth (i * n + j) matrix 0.

Definition MatrixValuesBounded (matrix : list Z) (n : Z) : Prop :=
  forall k, 0 <= k < n * n -> 1 <= Znth k matrix 0 <= 1000000.

Definition QueriesBounded
    (queries : list (Z * Z * Z * Z)) (n : Z) : Prop :=
  Forall (fun query =>
    let '(x1, y1, x2, y2) := query in
    0 <= x1 <= x2 /\ x2 < n /\ 0 <= y1 <= y2 /\ y2 < n) queries.

Definition RawQueriesEncode
    (queries : list (Z * Z * Z * Z)) (raw : list Z) : Prop :=
  Zlength raw = 4 * Zlength queries /\
  forall i,
    0 <= i < Zlength queries ->
    let '(x1, y1, x2, y2) := Znth i queries (0, 0, 0, 0) in
    Znth (4 * i) raw 0 = x1 + 1 /\
    Znth (4 * i + 1) raw 0 = y1 + 1 /\
    Znth (4 * i + 2) raw 0 = x2 + 1 /\
    Znth (4 * i + 3) raw 0 = y2 + 1.

Definition FlattenedWeightedSum
    (matrix : list Z) (n : Z) (query : Z * Z * Z * Z) (value : Z) : Prop :=
  let '(x1, y1, x2, y2) := query in
  value = fold_right Z.add 0
    (map (fun p =>
      let '(i, j) := p in
      MatrixCell matrix n i j *
        ((i - x1) * (y2 - y1 + 1) + (j - y1) + 1))
      (flat_map (fun i => map (fun j => (i, j)) (Zrange y1 (y2 + 1)))
                (Zrange x1 (x2 + 1)))).

Definition Spec (matrix : list Z) (n : Z)
    (queries : list (Z * Z * Z * Z)) (out : list Z) : Prop :=
  Forall2 (FlattenedWeightedSum matrix n) queries out.

Require Import Coq.micromega.Psatz.

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.micromega.Lia Coq.micromega.Psatz Coq.setoid_ring.Ring.
