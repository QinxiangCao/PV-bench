Require Export PVbench.Codeforces.examples_shard00.P071_2044H_hard_demon_problem.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.

Definition PrefixSumValue (matrix : list Z) (n r c : Z) : Z :=
  fold_right Z.add 0
    (flat_map (fun i =>
      map (fun j => MatrixCell matrix n i j) (Zrange 0 c))
      (Zrange 0 r)).

Definition PrefixRowValue (matrix : list Z) (n r c : Z) : Z :=
  fold_right Z.add 0
    (flat_map (fun i =>
      map (fun j => MatrixCell matrix n i j * (i + 1)) (Zrange 0 c))
      (Zrange 0 r)).

Definition PrefixColValue (matrix : list Z) (n r c : Z) : Z :=
  fold_right Z.add 0
    (flat_map (fun i =>
      map (fun j => MatrixCell matrix n i j * (j + 1)) (Zrange 0 c))
      (Zrange 0 r)).

Definition PrefixTables
    (matrix sums rows cols : list Z) (n stride upto : Z) : Prop :=
  Zlength sums = stride * stride /\
  Zlength rows = stride * stride /\
  Zlength cols = stride * stride /\
  (forall r,
    0 <= r < stride ->
    Znth (r * stride) sums 0 = 0 /\
    Znth (r * stride) rows 0 = 0 /\
    Znth (r * stride) cols 0 = 0) /\
  forall r c,
    0 <= r < stride ->
    0 <= c < stride ->
    r * stride + c < upto ->
    Znth (r * stride + c) sums 0 = PrefixSumValue matrix n r c /\
    Znth (r * stride + c) rows 0 = PrefixRowValue matrix n r c /\
    Znth (r * stride + c) cols 0 = PrefixColValue matrix n r c.

Definition RectLookup
    (values : list Z) (stride x1 y1 x2 y2 : Z) : Z :=
  Znth (x2 * stride + y2) values 0 -
  Znth ((x1 - 1) * stride + y2) values 0 -
  Znth (x2 * stride + y1 - 1) values 0 +
  Znth ((x1 - 1) * stride + y1 - 1) values 0.

Definition RectanglesBounded
    (values : list Z) (stride bound : Z) : Prop :=
  forall x1 y1 x2 y2,
    1 <= x1 <= x2 -> x2 < stride ->
    1 <= y1 <= y2 -> y2 < stride ->
    0 <= RectLookup values stride x1 y1 x2 y2 <= bound.

Definition RectIntermediatesSafe (values : list Z) (stride : Z) : Prop :=
  forall x1 y1 x2 y2,
    1 <= x1 <= x2 -> x2 < stride ->
    1 <= y1 <= y2 -> y2 < stride ->
    let upper_right := Znth (x2 * stride + y2) values 0 in
    let upper_left := Znth ((x1 - 1) * stride + y2) values 0 in
    let lower_right := Znth (x2 * stride + y1 - 1) values 0 in
    -9223372036854775808 <= upper_right - upper_left <= 9223372036854775807 /\
    -9223372036854775808 <=
      upper_right - upper_left - lower_right <= 9223372036854775807.

Definition QueryArithmeticSafe
    (sums rows cols : list Z) (stride x1 y1 x2 y2 : Z) : Prop :=
  let sm := RectLookup sums stride x1 y1 x2 y2 in
  let rs := RectLookup rows stride x1 y1 x2 y2 in
  let cs := RectLookup cols stride x1 y1 x2 y2 in
  0 <= rs - x1 * sm <= 4000000000000000 /\
  0 <= cs - (y1 - 1) * sm <= 4002000000000000 /\
  0 <= (y2 - y1 + 1) * (rs - x1 * sm) +
       cs - (y1 - 1) * sm <= 8000002000000000000.

Definition TablesReady
    (matrix sums rows cols : list Z) (n stride : Z) : Prop :=
  PrefixTables matrix sums rows cols n stride (stride * stride) /\
  RectanglesBounded sums stride 4000000000000 /\
  RectanglesBounded rows stride 4002000000000000 /\
  RectanglesBounded cols stride 4002000000000000 /\
  RectIntermediatesSafe sums stride /\
  RectIntermediatesSafe rows stride /\
  RectIntermediatesSafe cols stride /\
  forall x1 y1 x2 y2,
    1 <= x1 <= x2 -> x2 < stride ->
    1 <= y1 <= y2 -> y2 < stride ->
    QueryArithmeticSafe sums rows cols stride x1 y1 x2 y2.

Definition OutputPrefix
    (matrix : list Z) (n : Z) (queries : list (Z * Z * Z * Z))
    (out : list Z) (done : Z) : Prop :=
  Zlength out = done /\
  Forall2 (FlattenedWeightedSum matrix n) (sublist 0 done queries) out.

Require Import Coq.micromega.Psatz.

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.micromega.Lia Coq.micromega.Psatz Coq.setoid_ring.Ring.
